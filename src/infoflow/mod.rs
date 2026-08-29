pub mod aliasing;
pub mod backward;
pub mod cfg;
pub mod data;
pub mod forward;
pub mod ifds;
pub mod points_of_aliasing;

use std::collections::HashSet;

use data::access_path::AccessPath;
use log::*;
use rustc_middle::mir::{self as rustc_mir, Location, Operand, Place, TerminatorKind};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_abi::FieldIdx;
use smallvec::{smallvec, SmallVec};

use crate::analysis_context::AnalysisContext;
use crate::graph::call_graph;
use crate::mir::function::FuncDef;
use crate::mir::place_ext::PlaceExt;
pub use crate::mir::unit::{Unit, StatementOrTerminator, statement_or_terminator_at};
use crate::util::type_util;
use crate::util::generics_specializer::GenericsSpecializer;
pub use crate::mir::builtins::{is_alloc, is_realloc, is_dealloc, dealloc_arg, realloc_arg_and_dst};


pub type CallGraph<'tcx> = call_graph::CallGraph<FuncDef<'tcx>, call_graph::CallSite<'tcx>>;

pub enum Direction {
    Forward,
    Backward,
}


#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PointerFlowOrigin<'tcx> {
    pub kind: FlowOriginKind<'tcx>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FlowOriginKind<'tcx> {
    // The origin is a reference to a place in the current function.
    Reference {
        ref_path: AccessPath<'tcx>,
        location: Location,
    },
    // A heap object allocated via a alloc function.
    Allocation {
        path: AccessPath<'tcx>,
        alloc_trace: &'tcx [Unit<'tcx>],
    },
    // The allocation site of the pointer is not found in the current
    // function nor any of its transitively reachable callees; the
    // source has been allocated in its caller context.
    Parameter(AccessPath<'tcx>),
}

impl<'tcx> PointerFlowOrigin<'tcx> {
    pub fn new(kind: FlowOriginKind<'tcx>) -> Self {
        PointerFlowOrigin { kind }
    }

    pub fn new_reference(ref_path: AccessPath<'tcx>, location: Location) -> Self {
        PointerFlowOrigin {
            kind: FlowOriginKind::Reference { ref_path, location },
        }
    }

    pub fn new_allocation(path: AccessPath<'tcx>, alloc_trace: &'tcx [Unit<'tcx>]) -> Self {
        PointerFlowOrigin {
            kind: FlowOriginKind::Allocation { path, alloc_trace },
        }
    }

    pub fn new_parameter(path: AccessPath<'tcx>) -> Self {
        PointerFlowOrigin {
            kind: FlowOriginKind::Parameter(path),
        }
    }
}


/// Map each argument to its corresponding parameter in the callee.
/// The n-th argument may not map to the n-th parameter for a Fn-trait call.
/// If the callee's mir is not available, we return an empty vector.
pub fn arg_param_pairs<'tcx>(
    acx: &AnalysisContext<'tcx>,
    callsite: Unit<'tcx>,
    callee: FuncDef<'tcx>,
) -> Vec<(Operand<'tcx>, Place<'tcx>)> {
    let mut pairs = Vec::new();
    let caller_mir = acx.tcx.optimized_mir(callsite.func.def_id);
    let callee_mir = if acx.tcx.is_mir_available(callee.def_id) {
        acx.tcx.optimized_mir(callee.def_id)
    } else {
        return pairs;
    };

    // Retrieve the terminator at the given location
    let args = callsite.call_args(acx.tcx);
    let params = callee_mir
        .args_iter()
        .map(|local| Place::from(local))
        .collect::<Vec<Place<'tcx>>>();

    if params.is_empty() {
        return pairs;
    }

    // A `Fn*` call receive two arguments:
    // 1. An operand of any type that implements `Fn`|`FnMut`|`FnOnce`, including
    //    function items, function pointers and closures.
    // 2. A tuple of arguments to be passed to the function.
    // In cases of function items, function pointers and closures, we need to
    // unpack the tuple to pair each argument with its corresponding parameter.
    if is_fntrait_call(acx, callsite) {
        assert_eq!(args.len(), 2);

        // For simplicity, we detemine if we need to unpack the arguments by
        // checking if the callee takes two arguments and the second argument
        // is a tuple.
        let param_tys = params
            .iter()
            .map(|param| param.ty(callee_mir, acx.tcx).ty)
            .collect::<Vec<Ty<'tcx>>>();
        if params.len() != 2 || !matches!(param_tys[1].kind(), TyKind::Tuple(_)) {
            match args[1] {
                Operand::Copy(args_tuple) | Operand::Move(args_tuple) => {
                    if let TyKind::Tuple(tuple_types) = args_tuple.ty(caller_mir, acx.tcx).ty.kind()
                    {
                        if tuple_types.len() != params.len() - 1 {
                            warn!(
                                "Mismatched number of arguments and parameters at {:?}",
                                callsite
                            );
                            return pairs;
                        }
                        let unpacked_args = tuple_types
                            .iter()
                            .enumerate()
                            .map(|(i, ty)| {
                                Operand::Copy(acx.tcx.mk_place_field(
                                    args_tuple,
                                    FieldIdx::from_usize(i),
                                    ty,
                                ))
                            })
                            .collect::<Vec<Operand<'tcx>>>();

                        // TODO: Call_once consumes its callee argument, but the callee
                        // may take a reference to the closure instead of consuming it.
                        // We need to map args[0] to *params[0] in this case.
                        if !args[0].ty(caller_mir, acx.tcx).is_ref() && param_tys[0].is_ref() {
                        } else {
                            pairs.push((args[0].clone(), params[0]));
                        }

                        for i in 0..tuple_types.len() {
                            pairs.push((unpacked_args[i].clone(), params[i + 1]));
                        }
                        return pairs;
                    } else {
                        debug!(
                            "Expect a tuple argument at {:?}, found {:?}",
                            callsite, args_tuple
                        );
                        return pairs;
                    }
                }
                _ => {
                    // TODO: Call_once consumes its callee argument, but the callee
                    // may take a reference to the closure instead of consuming it.
                    // We need to map args[0] to *params[0] in this case.
                    if !args[0].ty(caller_mir, acx.tcx).is_ref() && param_tys[0].is_ref() {
                    } else {
                        pairs.push((args[0].clone(), params[0]));
                    }
                    return pairs;
                }
            }
        }
    }

    // TODO: add support for thread spawn functions

    if args.len() != params.len() {
        warn!(
            "Mismatched number of arguments and parameters at {:?}",
            callsite
        );
        return pairs;
    }

    for (arg, param) in args.iter().zip(params.iter()) {
        pairs.push((arg.clone(), param.clone()));
    }
    pairs
}

pub fn is_fntrait_call<'tcx>(acx: &AnalysisContext<'tcx>, callsite: Unit<'tcx>) -> bool {
    match statement_or_terminator_at(acx.tcx, callsite) {
        StatementOrTerminator::Statement(_) => false,
        StatementOrTerminator::Terminator(terminator) => match terminator {
            TerminatorKind::Call { func, .. } => match func {
                Operand::Constant(box constant) => match constant.ty().kind() {
                    TyKind::FnDef(callee_id, _) => acx.is_std_ops_fntrait_call(*callee_id),
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        },
    }
}

/// Returns the left-hand side place of an assignment at the given unit, if any.
pub fn get_lplace_of_assignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    unit: Unit<'tcx>,
) -> Option<&'tcx rustc_mir::Place<'tcx>> {
    match statement_or_terminator_at(tcx, unit) {
        StatementOrTerminator::Statement(stmt) => match stmt {
            rustc_mir::StatementKind::Assign(box (place, _)) => Some(place),
            _ => None,
        },
        _ => None,
    }
}

/// Applies flow function logic for an assignment statement's rvalue.
/// Used by both backward and forward `get_normal_flow_function` to avoid
/// duplicating the rvalue match skeleton.
///
/// Returns `Some(results)` for handled rvalue arms, `None` for arms that
/// need direction-specific handling (Cast non-pointer, CoroutineClosure, etc.)
/// so callers can fall through to their own logic.
///
/// - `move_or_copy` / `ref_or_rawptr`: direction-specific compute callbacks.
/// - `aggr_fields`: called for multi-field aggregates (Adt struct/enum,
///   Tuple/Closure/Coroutine) after the shared setup builds `(field_place, operand)`
///   pairs. The callback implements direction-specific field matching strategy.
///   Array and union aggregates are handled directly via `move_or_copy`.
pub fn apply_assignment_flow<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: FuncDef<'tcx>,
    lplace: &rustc_mir::Place<'tcx>,
    rvalue: &rustc_mir::Rvalue<'tcx>,
    source: &AccessPath<'tcx>,
    curr: Unit<'tcx>,
    move_or_copy: &impl Fn(
        &AccessPath<'tcx>, 
        &rustc_mir::Place<'tcx>, 
        &rustc_mir::Operand<'tcx>, 
        Unit<'tcx>
    ) -> SmallVec<[AccessPath<'tcx>; 1]>,
    ref_or_rawptr: &impl Fn(
        &AccessPath<'tcx>, 
        &rustc_mir::Place<'tcx>, 
        &rustc_mir::Place<'tcx>, 
        Unit<'tcx>, 
        bool
    ) -> SmallVec<[AccessPath<'tcx>; 1]>,
    aggr_fields: &impl Fn(
        &AccessPath<'tcx>,
        rustc_mir::Place<'tcx>,
        &[(rustc_mir::Place<'tcx>, rustc_mir::Operand<'tcx>)],
        Unit<'tcx>,
    ) -> SmallVec<[AccessPath<'tcx>; 1]>,
) -> Option<SmallVec<[AccessPath<'tcx>; 1]>> {
    match rvalue {
        rustc_mir::Rvalue::Use(operand) => {
            Some(move_or_copy(source, lplace, operand, curr))
        }
        // Creates an array where each element is the value of the operand.
        // Corresponds to source code like [x; 32].
        // It can be treated as an assignment lplace.index = operand.
        rustc_mir::Rvalue::Repeat(operand, _count) => {
            let index_place = tcx.mk_place_elem(
                *lplace,
                rustc_mir::PlaceElem::ConstantIndex {
                    offset: 0,
                    min_length: 0,
                    from_end: false,
                },
            );
            Some(move_or_copy(source, &index_place, operand, curr))
        }
        // Creates a reference to a place.
        // Corresponds to source code like &x.f and &(*x).f.
        rustc_mir::Rvalue::Ref(_, _, rplace) => {
            Some(ref_or_rawptr(source, lplace, rplace, curr, false))
        }
        // Creates a raw pointer with the indicated mutability to the place.
        // This is generated by pointer casts like &v as *const _ or raw borrow expressions
        // like &raw const v.
        rustc_mir::Rvalue::RawPtr(_, rplace) => {
            Some(ref_or_rawptr(source, lplace, rplace, curr, true))
        }
        // Creates an aggregate value, like a tuple or struct.
        rustc_mir::Rvalue::Aggregate(aggregate_kind, operands) => {
            match aggregate_kind.as_ref() {
                // Array: identical in both directions — collect all element flows.
                rustc_mir::AggregateKind::Array(_ty) => {
                    let mut dtargets = HashSet::new();
                    for (i, operand) in operands.iter().enumerate() {
                        let index_place = tcx.mk_place_elem(
                            *lplace,
                            rustc_mir::PlaceElem::ConstantIndex {
                                offset: i as u64,
                                min_length: 1,
                                from_end: false,
                            },
                        );
                        dtargets.extend(
                            &move_or_copy(source, &index_place, operand, curr),
                        );
                    }
                    Some(dtargets.into_iter().collect())
                }
                rustc_mir::AggregateKind::Adt(def, variant_idx, args, _, case_index) => {
                    let args = GenericsSpecializer::new(tcx, func.generic_args)
                        .specialize_generic_args(args);
                    let adt_def = tcx.adt_def(def);
                    let variant_def = &adt_def.variants()[*variant_idx];
                    let mut adt_place = *lplace;

                    // The second field is the variant index. It's equal to 0 for struct
                    // and union expressions. The last field is the active field number
                    // and is present only for union expressions – e.g., for a union
                    // expression SomeUnion { c: .. }, the active field index would
                    // identity the field c
                    if adt_def.is_union() {
                        let case_index = case_index.unwrap_or(FieldIdx::from_usize(0));
                        let field = &variant_def.fields[case_index];
                        let field_ty = type_util::field_ty(tcx, field, args);
                        let union_field = tcx.mk_place_field(
                            *lplace,
                            case_index,
                            field_ty,
                        );
                        return Some(move_or_copy(
                            source,
                            &union_field,
                            &operands[FieldIdx::from_usize(0)],
                            curr,
                        ));
                    } else if adt_def.is_enum() {
                        adt_place =
                            tcx.mk_place_downcast(adt_place, adt_def, *variant_idx);
                    }

                    // Struct/enum: build field pairs, delegate to callback.
                    let field_pairs: Vec<_> = (0..operands.len())
                        .filter_map(|field| {
                            let field_idx = FieldIdx::from_usize(field);
                            let field_ty = type_util::field_ty(
                                tcx,
                                &variant_def.fields[field_idx],
                                args,
                            );
                            if type_util::is_zst(tcx, field_ty) {
                                return None;
                            }
                            let operand = operands.get(field_idx).unwrap();
                            let field_place = tcx.mk_place_field(
                                adt_place,
                                field_idx,
                                field_ty,
                            );
                            Some((field_place, operand.clone()))
                        })
                        .collect();

                    Some(aggr_fields(source, adt_place, &field_pairs, curr))
                }
                rustc_mir::AggregateKind::Tuple
                | rustc_mir::AggregateKind::Closure(..)
                | rustc_mir::AggregateKind::Coroutine(..) => {
                    let lplace_ty = type_util::place_ty(tcx, lplace, func);
                    let field_pairs: Vec<_> = (0..operands.len())
                        .filter_map(|field| {
                            let field_idx = FieldIdx::from_usize(field);
                            let field_ty =
                                type_util::get_field_type(tcx, lplace_ty, field);
                            if type_util::is_zst(tcx, field_ty) {
                                return None;
                            }
                            let operand = operands.get(field_idx).unwrap();
                            let field_place = tcx.mk_place_field(
                                *lplace,
                                field_idx,
                                field_ty,
                            );
                            Some((field_place, operand.clone()))
                        })
                        .collect();

                    Some(aggr_fields(source, *lplace, &field_pairs, curr))
                }
                rustc_mir::AggregateKind::RawPtr(_ty, _mutbl) => {
                    if let Some(operand) = operands.get(FieldIdx::from_usize(0)) {
                        Some(move_or_copy(source, lplace, operand, curr))
                    } else {
                        Some(smallvec![])
                    }
                }
                // CoroutineClosure differs between directions.
                rustc_mir::AggregateKind::CoroutineClosure(..) => None,
            }
        }
        // Transmutes a *mut u8 into shallow-initialized Box<T>.
        rustc_mir::Rvalue::ShallowInitBox(operand, ty) => {
            // The type is the dereferenced type of the Box, i.e. T in Box<T>.
            let box_ty = Ty::new_box(tcx, *ty);
            let box_ptr = lplace.box_ptr_field(tcx, box_ty);
            Some(move_or_copy(source, &box_ptr, operand, curr))
        }
        rustc_mir::Rvalue::Cast(cast_kind, operand, _ty) => {
            match cast_kind {
                // Go from a mut raw pointer to a const raw pointer.
                rustc_mir::CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _)
                // Unsize a pointer/reference value, e.g., &[T; n] to &[T]. Note that the source
                // could be a thin or fat pointer.
                | rustc_mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _)
                // Go from *const [T; N] to *const T
                // In practice, we find that most casts from *const [T; N] to *const T are
                // classified as CastKind::PtrToPtr
                | rustc_mir::CastKind::PointerCoercion(PointerCoercion::ArrayToPointer, _)
                | rustc_mir::CastKind::PtrToPtr => {
                    // With index-based representation for access paths, we treat cast as direct assignment.
                    Some(move_or_copy(source, lplace, operand, curr))
                }
                // Non-pointer casts differ between backward and forward
                _ => None,
            }
        }
        // A CopyForDeref is equivalent to a read from a place at the codegen level,
        // but is treated specially by drop elaboration. When such a read happens,
        // it is guaranteed (via nature of the mir_opt `Derefer` in
        // rustc_mir_transform/src/deref_separator) that the only use of the returned
        // value is a deref operation, immediately followed by one or more projections.
        // Drop elaboration treats this rvalue as if the read never happened and just
        // projects further.
        // For example, if we have `let x = *m.f;`, where f is a Box type field of m,
        // the compiler will generate a `deref_copy` statement
        // `tmp = deref_copy (m.f: std::boxed::Box<T>);` and then a load statement
        // `x = *tmp;`.
        rustc_mir::Rvalue::CopyForDeref(rplace) => {
            // We treat the `deref_copy` statement as a direct assignment.
            Some(move_or_copy(
                source,
                lplace,
                &rustc_mir::Operand::Copy(*rplace),
                curr,
            ))
        }
        rustc_mir::Rvalue::BinaryOp(bin_op, box (first_operand, _second_operand)) => {
            if let rustc_mir::BinOp::Offset = bin_op {
                // Treat the offset operation as a direct assignment.
                Some(move_or_copy(source, lplace, first_operand, curr))
            } else {
                None
            }
        }
        // No-ops: no pointer flow through these
        rustc_mir::Rvalue::UnaryOp(..)
        | rustc_mir::Rvalue::Discriminant(..) => None,
        _ => None,
    }
}

/// Determines if an access path should be retained for propagation.
/// Filters out access paths that exceed the configured dereference depth limit.
pub fn retain_access_path<'tcx>(acx: &AnalysisContext<'tcx>, d: &AccessPath<'tcx>) -> bool {
    let valid = d.deref_count() <= acx.analysis_options.access_path_deref_limit;
    if !valid {
        acx.add_dropped_access_path(d.clone());
    }
    valid
}
