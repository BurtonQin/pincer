use rustc_hir::def_id::DefId;
use rustc_hir::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    self, BasicBlock, BasicBlockData, Body, Local, LocalDecl, Operand, Place, PlaceElem,
    Rvalue, SourceInfo, SourceScopeData, Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{Instance, InstanceKind, Ty, TyCtxt, TyKind, TypeVisitableExt};
use rustc_span::{source_map::Spanned, DUMMY_SP};
use std::cell::RefCell;
use std::collections::HashMap;

use crate::mir::function::FuncDef;
use crate::mir::projection::PlaceElems;
use crate::util::type_util;

/// Metadata for a drop shim, with its cached MIR body.
#[derive(Debug, Clone, Copy)]
pub struct DropShim<'tcx> {
    pub ty: Ty<'tcx>,
    pub func_def: FuncDef<'tcx>,
    /// Cached MIR body for this drop shim
    pub body: &'tcx Body<'tcx>,
}

/// Cache of resolved drop shim bodies, keyed by FuncDef.
/// Uses interior mutability so all access is through `&self`.
pub struct DropShims<'tcx> {
    cache: RefCell<HashMap<FuncDef<'tcx>, DropShim<'tcx>>>,
}

impl<'tcx> DropShims<'tcx> {
    pub fn new() -> Self {
        DropShims { cache: RefCell::new(HashMap::new()) }
    }

    /// Get the drop shim body, resolving and caching on demand.
    pub fn body(&self, tcx: TyCtxt<'tcx>, func_def: FuncDef<'tcx>) -> &'tcx Body<'tcx> {
        if let Some(shim) = self.cache.borrow().get(&func_def) {
            return shim.body;
        }
        let ty = func_def.generic_args[0].expect_ty();
        let body = resolve_drop_shim_body(tcx, ty);
        self.cache.borrow_mut().insert(func_def, DropShim { ty, func_def, body });
        body
    }
}

/// Returns the DefId of `drop_in_place` (lang item).
/// Used as the identifier for drop shim FuncDefs so that explicit
/// `drop_in_place` calls naturally produce matching FuncDefs.
pub fn drop_shim_def_id(tcx: TyCtxt<'_>) -> DefId {
    tcx.require_lang_item(LangItem::DropInPlace, rustc_span::DUMMY_SP)
}

/// Creates a `FuncDef` representing a drop shim for `ty`.
pub fn drop_func_def<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> FuncDef<'tcx> {
    let def_id = drop_shim_def_id(tcx);
    let gen_args = tcx.mk_args(&[ty.into()]);
    FuncDef::new_func_def(def_id, gen_args)
}

/// Returns true if `func_def` is a drop shim (uses `drop_in_place` DefId).
pub fn is_drop_shim(tcx: TyCtxt<'_>, func_def: FuncDef<'_>) -> bool {
    func_def.def_id == drop_shim_def_id(tcx)
}

pub fn is_rc_drop_shim<'tcx>(tcx: TyCtxt<'tcx>, func_def: FuncDef<'tcx>) -> bool {
    is_drop_shim(tcx, func_def)
        && type_util::is_reference_counting_pointer(
            tcx,
            func_def.generic_args[0].as_type().unwrap(),
        )
}


/// Construct a fallback drop body for a non-concrete type.
/// The body follows the same convention as rustc's drop shim:
/// `_1: *mut T` is the parameter, and field drops use `(*_1).field`.
fn make_fallback_drop_body<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> &'tcx Body<'tcx> {

    let mut basic_blocks_data = IndexVec::new();
    let mut local_decls: IndexVec<Local, LocalDecl<'tcx>> = IndexVec::new();

    // _0: () (return place)
    local_decls.push(LocalDecl::new(Ty::new_tup(tcx, &[]), DUMMY_SP));
    // _1: *mut T (parameter - matches shim convention)
    local_decls.push(LocalDecl::new(Ty::new_mut_ptr(tcx, ty), DUMMY_SP));

    let local_1 = Local::from_usize(1);
    let is_manually_drop = type_util::is_manually_drop(ty);
    let mut curr_block = 0usize;

    // If T: Drop, add a Call to the drop impl
    if let Some((drop_impl, drop_gen_args)) = type_util::find_drop_impl(tcx, ty) {
        // _2: &mut T (reference for the drop call)
        local_decls.push(LocalDecl::new(
            Ty::new_ref(
                tcx,
                tcx.lifetimes.re_erased,
                ty,
                rustc_middle::ty::Mutability::Mut,
            ),
            DUMMY_SP,
        ));
        // _3: () (destination of the drop impl call)
        local_decls.push(LocalDecl::new(Ty::new_tup(tcx, &[]), DUMMY_SP));

        let local_2 = Local::from_usize(2);
        let local_3 = Local::from_usize(3);

        // _2 = &mut (*_1)
        let ref_assign = Statement::new(
            SourceInfo::outermost(DUMMY_SP),
            StatementKind::Assign(Box::new((
                local_2.into(),
                Rvalue::Ref(
                    tcx.lifetimes.re_erased,
                    mir::BorrowKind::Mut {
                        kind: mir::MutBorrowKind::Default,
                    },
                    tcx.mk_place_deref(Place::from(local_1)),
                ),
            ))),
        );

        // Call <T as Drop>::drop(move _2) -> next_block
        let drop_call = Terminator {
            source_info: SourceInfo::outermost(DUMMY_SP),
            kind: TerminatorKind::Call {
                func: Operand::Constant(Box::new(mir::ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: mir::Const::Val(
                        mir::ConstValue::ZeroSized,
                        Ty::new_fn_def(tcx, drop_impl, drop_gen_args),
                    ),
                })),
                args: Box::new([Spanned {
                    span: DUMMY_SP,
                    node: Operand::Copy(local_2.into()),
                }]),
                destination: Place::from(local_3),
                target: Some(BasicBlock::from_usize(curr_block + 1)),
                unwind: mir::UnwindAction::Continue,
                call_source: mir::CallSource::Misc,
                fn_span: DUMMY_SP,
            },
        };

        basic_blocks_data.push(BasicBlockData::new_stmts(
            vec![ref_assign],
            Some(drop_call),
            false,
        ));
        curr_block += 1;
    }

    // For each field that needs drop, add a Drop terminator
    if !is_manually_drop {
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
        for (fld_proj, field_ty) in get_field_and_types(tcx, ty) {
            // needs_drop ICEs on types containing alias projections
            // (e.g., Vec<A::Assoc>) because rustc cannot normalize them.
            // Skip the check for such types — conservatively assume they need drop.
            if !type_util::contains_alias_projection(tcx, field_ty)
                && !field_ty.needs_drop(tcx, typing_env)
            {
                continue;
            }

            // Place: (*_1).field — deref the pointer, then project to the field
            let mut projection = vec![PlaceElem::Deref];
            projection.extend_from_slice(fld_proj);
            let fld_place = Place {
                local: local_1,
                projection: tcx.mk_place_elems(&projection),
            };

            let fld_drop = Terminator {
                source_info: SourceInfo::outermost(DUMMY_SP),
                kind: TerminatorKind::Drop {
                    place: fld_place,
                    target: BasicBlock::from_usize(curr_block + 1),
                    unwind: mir::UnwindAction::Continue,
                    replace: false,
                    // Cleanup to be done if the coroutine is dropped at this suspend point (for async drop).
                    drop: None,
                    // Prepared async future local (for async drop).
                    async_fut: None,
                },
            };

            basic_blocks_data.push(BasicBlockData::new_stmts(
                Vec::new(),
                Some(fld_drop),
                false,
            ));
            curr_block += 1;
        }
    }

    // Return block
    basic_blocks_data.push(BasicBlockData::new_stmts(
        Vec::new(),
        Some(Terminator {
            source_info: SourceInfo::outermost(DUMMY_SP),
            kind: TerminatorKind::Return,
        }),
        false,
    ));

    // Minimal source_scopes (required by Body::new)
    let mut source_scopes = IndexVec::new();
    source_scopes.push(SourceScopeData {
        span: DUMMY_SP,
        parent_scope: None,
        inlined: None,
        inlined_parent_scope: None,
        local_data: rustc_middle::mir::ClearCrossCrate::Clear,
    });

    let body = Body::new(
        rustc_middle::mir::MirSource::item(drop_shim_def_id(tcx)),
        basic_blocks_data,
        source_scopes,
        local_decls,
        rustc_middle::ty::CanonicalUserTypeAnnotations::default(),
        1, // arg_count (_1 is the single argument)
        Vec::new(),
        DUMMY_SP,
        None,
        None,
    );

    tcx.arena.alloc(body)
}

/// Get the rustc-generated drop shim body for a type.
/// For most types (including generic ones with type params), uses rustc's native
/// drop shim generator. For types containing alias projections (e.g., `<A as Trait>::Assoc`),
/// constructs a fallback body since rustc ICEs on those.
pub fn resolve_drop_shim_body<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> &'tcx Body<'tcx> {
    let def_id = tcx.require_lang_item(LangItem::DropInPlace, rustc_span::DUMMY_SP);
    let noop = || tcx.instance_mir(InstanceKind::DropGlue(def_id, None));

    // Types containing alias projections (e.g., Vec<A::Assoc>) cause ICEs in
    // rustc's drop shim generator because it cannot normalize them.
    // Use a fallback body for these types.
    if type_util::contains_alias_projection(tcx, ty) {
        return make_fallback_drop_body(tcx, ty);
    }

    // Types with unresolved params (e.g., const generic params) can cause panics inside
    // rustc's query system that leave queries in an active state, breaking incremental cache.
    if ty.has_param() {
        return make_fallback_drop_body(tcx, ty);
    }

    // Wrap resolution + shim generation in catch_unwind as a safety net.
    // tcx.instance_mir can ICE for certain complex types.
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let args = tcx.mk_args(&[ty.into()]);
        match Instance::try_resolve(
            tcx,
            rustc_middle::ty::TypingEnv::fully_monomorphized(),
            def_id,
            args,
        ) {
            Ok(Some(instance)) => tcx.instance_mir(instance.def),
            _ => noop(),
        }
    }))
    .unwrap_or_else(|_| noop())
}

/// Get the rustc-generated drop shim body for a drop shim FuncDef.
pub fn drop_shim_body<'tcx>(tcx: TyCtxt<'tcx>, func_def: FuncDef<'tcx>) -> &'tcx Body<'tcx> {
    let ty = func_def.generic_args[0].expect_ty();
    resolve_drop_shim_body(tcx, ty)
}

/// Getting all field and field types from a type
pub fn get_field_and_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<(PlaceElems<'tcx>, Ty<'tcx>)> {
    let mut fld_and_tys = Vec::new();
    match ty.kind() {
        TyKind::Adt(adt_def, args) if adt_def.is_struct() || adt_def.is_union() => {
            let variant = adt_def
                .variants()
                .iter()
                .next()
                .expect("at least one variant");
            for (field_idx, field_def) in variant.fields.iter_enumerated() {
                let field_ty = type_util::field_ty(tcx, field_def, args);
                let place_elem = PlaceElem::Field(field_idx, field_ty);
                let fld_proj = tcx.mk_place_elems(&[place_elem]);
                fld_and_tys.push((fld_proj, field_ty));
            }
        }
        TyKind::Adt(adt_def, args) if adt_def.is_enum() => {
            for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                let downcast = PlaceElem::Downcast(Some(variant.name), variant_idx);
                for (field_idx, field_def) in variant.fields.iter_enumerated() {
                    let field_ty = type_util::field_ty(tcx, field_def, args);
                    let place_elem = PlaceElem::Field(field_idx, field_ty);
                    let fld_proj = tcx.mk_place_elems(&[downcast, place_elem]);
                    fld_and_tys.push((fld_proj, field_ty));
                }
            }
        }
        TyKind::Array(elem_ty, _) | TyKind::Slice(elem_ty) => {
            let const_idx = PlaceElem::ConstantIndex {
                offset: 0,
                min_length: 0,
                from_end: false,
            };
            let fld_proj = tcx.mk_place_elems(&[const_idx]);
            fld_and_tys.push((fld_proj, *elem_ty));
        }
        TyKind::Tuple(tuple_types) => {
            for (field_idx, field_ty) in tuple_types.iter().enumerate() {
                let place_elem = PlaceElem::Field(field_idx.into(), field_ty);
                let fld_proj = tcx.mk_place_elems(&[place_elem]);
                fld_and_tys.push((fld_proj, field_ty));
            }
        }
        TyKind::Closure(..) | TyKind::Coroutine(..) => {
            let closure_field_types = type_util::closure_field_types(ty);
            for (field_idx, field_ty) in closure_field_types.iter().enumerate() {
                let place_elem = PlaceElem::Field(field_idx.into(), *field_ty);
                let fld_proj = tcx.mk_place_elems(&[place_elem]);
                fld_and_tys.push((fld_proj, *field_ty));
            }
        }
        _ => {}
    }

    fld_and_tys
}
