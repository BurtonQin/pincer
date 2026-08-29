// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use log::*;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Place;
use rustc_middle::ty::{
    CoroutineArgsExt, ExistentialPredicate, FieldDef, FnSigTys, ParamEnv, Ty, TyCtxt, TyKind,
    TypeVisitableExt,
};
use rustc_middle::ty::{GenericArgKind, GenericArgsRef};
use rustc_abi::{FieldIdx, VariantIdx};

use crate::mir::drop_shim;
use crate::mir::function::FuncDef;
use crate::mir::known_names::{KnownNames, KnownNamesCache};
use crate::util::generics_specializer::GenericsSpecializer;

/// Returns the target type of a reference type.
pub fn get_dereferenced_type(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) => *ty,
        TyKind::Ref(_, ty, _) => *ty,
        _ => {
            if ty.is_box() {
                ty.boxed_ty().unwrap()
            } else {
                ty
            }
        }
    }
}

/// Returns the element type of an array or slice type.
pub fn get_element_type<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    match &ty.kind() {
        TyKind::Array(t, _) => *t,
        TyKind::RawPtr(t, ..) | TyKind::Ref(_, t, _) => match t.kind() {
            TyKind::Array(t, _) => *t,
            TyKind::Slice(t) => *t,
            TyKind::Str => tcx.types.char,
            _ => *t,
        },
        TyKind::Slice(t) => *t,
        TyKind::Str => tcx.types.char,
        _ => ty,
    }
}

/// Returns the type of the field with the given ordinal.
pub fn get_field_type<'tcx>(tcx: TyCtxt<'tcx>, base_ty: Ty<'tcx>, ordinal: usize) -> Ty<'tcx> {
    if let TyKind::Adt(def, args) = base_ty.kind() {
        if def.is_union() || def.is_struct() {
            let variant = def.variants().iter().next().expect("at least one variant");
            assert!(ordinal < variant.fields.len());
            let field = &variant.fields[FieldIdx::from_usize(ordinal)];
            let ft = field_ty(tcx, field, args);
            return ft;
        } else {
            warn!(
                "Getting the field type with ordinal {:?} for a Enum type {:?} ",
                ordinal, base_ty
            );
            return tcx.types.never;
        }
    } else if let TyKind::Tuple(tuple_types) = base_ty.kind() {
        assert!(ordinal < tuple_types.len());
        let ft = tuple_types[ordinal];
        return ft;
    } else if base_ty.is_closure() || base_ty.is_coroutine() {
        let closure_field_types = closure_field_types(base_ty);
        trace!("Closure/Coroutine field types: {:?}", closure_field_types);
        assert!(ordinal < closure_field_types.len());
        return closure_field_types[ordinal];
    } else {
        warn!(
            "Getting the field type for an unexpected type {:?} ",
            base_ty
        );
        return tcx.types.never;
    }
}

/// Returns the rustc TyKind of the downcast projection
pub fn get_downcast_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    variant_idx: VariantIdx,
) -> Ty<'tcx> {
    if let TyKind::Adt(def, args) = base_ty.kind() {
        let variant = if variant_idx.index() >= def.variants().len() {
            warn!(
                "illegally down casting to index {} of {:?}",
                variant_idx.index(),
                base_ty,
            );
            // Return the last variant type of the enum
            &def.variants().iter().last().unwrap()
        } else {
            def.variant(variant_idx)
        };
        let field_tys = variant
            .fields
            .iter()
            .map(|field| field_ty(tcx, field, args));
        Ty::new_tup_from_iter(tcx, field_tys)
    } else if let TyKind::Coroutine(def_id, args) = base_ty.kind() {
        let mut tuple_types = args.as_coroutine().state_tys(*def_id, tcx);
        if let Some(field_tys) = tuple_types.nth(variant_idx.index()) {
            return Ty::new_tup_from_iter(tcx, field_tys);
        }
        debug!(
            "illegally down casting to index {} of {:?}",
            variant_idx.index(),
            base_ty,
        );
        tcx.types.never
    } else {
        warn!("unexpected type for downcast {:?}", base_ty);
        tcx.types.never
    }
}

pub fn specialize_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    generic_args: GenericArgsRef<'tcx>,
) -> Ty<'tcx> {
    let generics_specializer = GenericsSpecializer::new(tcx, generic_args);
    generics_specializer.specialize_generic_argument_type(ty)
}

pub fn place_ty<'tcx>(tcx: TyCtxt<'tcx>, place: &Place<'tcx>, func: FuncDef<'tcx>) -> Ty<'tcx> {
    if drop_shim::is_drop_shim(tcx, func) {
        let body = drop_shim::drop_shim_body(tcx, func);
        place.ty(&body.local_decls, tcx).ty
    } else {
        let ty = place.ty(tcx.optimized_mir(func.def_id), tcx).ty;
        specialize_generic_args(tcx, ty, func.generic_args)
    }
}

pub fn field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    field: &FieldDef,
    generic_args: GenericArgsRef<'tcx>,
) -> Ty<'tcx> {
    // CHECKME: Compare the following three ways to get the field type
    // 1.
    // let ft = field.ty(tcx, generic_args);

    // 2.
    // let field_ty = tcx.type_of(field.did).skip_binder();
    // let generics_specializer = GenericsSpecializer::new(tcx, generic_args);
    // tcx.erase_regions_ty(generics_specializer.specialize_generic_argument_type(field_ty))

    tcx.type_of(field.did).instantiate(tcx, generic_args)
}

/// Returns false if any of the generic arguments are themselves generic
pub fn are_concrete(generic_args: GenericArgsRef<'_>) -> bool {
    for gen_arg in generic_args.iter() {
        if let GenericArgKind::Type(ty) = gen_arg.kind() {
            if !is_concrete(ty.kind()) {
                return false;
            }
        }
    }
    true
}

/// Determines if the given type is fully concrete.
pub fn is_concrete(ty_kind: &TyKind<'_>) -> bool {
    match ty_kind {
        TyKind::Adt(_, gen_args)
        | TyKind::Closure(_, gen_args)
        | TyKind::FnDef(_, gen_args)
        | TyKind::Coroutine(_, gen_args)
        | TyKind::CoroutineWitness(_, gen_args)
        | TyKind::Alias(_, rustc_middle::ty::AliasTy { args: gen_args, .. }) => {
            are_concrete(gen_args)
        }
        TyKind::Tuple(types) => types.iter().all(|t| is_concrete(t.kind())),
        TyKind::Bound(..)
        | TyKind::Dynamic(..)
        | TyKind::Error(..)
        | TyKind::Infer(..)
        | TyKind::Param(..) => false,
        TyKind::Ref(_, ty, _) => is_concrete(ty.kind()),
        _ => true,
    }
}

/// Returns true if this id corresponds to the fn_trait|fn_mut_trait|fn_once_trait
pub fn is_fn_trait(tcx: TyCtxt<'_>, id: DefId) -> bool {
    let items = tcx.lang_items();
    match Some(id) {
        x if x == items.fn_trait() => true,
        x if x == items.fn_mut_trait() => true,
        x if x == items.fn_once_trait() => true,
        _ => false,
    }
}

/// Returns true if this type is `dyn Fn`, `dyn FnMut` or  `dyn FnOnce`.
pub fn is_dynamic_fn_trait<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    if let TyKind::Dynamic(trait_data, ..) = ty.kind() {
        if let Some(principal) = trait_data.principal() {
            let principal = tcx.normalize_erasing_late_bound_regions(
                rustc_middle::ty::TypingEnv::fully_monomorphized(),
                principal,
            );
            return is_fn_trait(tcx, principal.def_id);
        }
    }
    return false;
}

pub fn is_fn_once_output<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> bool {
    let items = tcx.lang_items();
    match Some(id) {
        x if x == items.fn_once_output() => true,
        _ => false,
    }
}

pub fn is_fn_once_call_once<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> bool {
    matches!(
        KnownNamesCache::get_known_name_for(tcx, id),
        KnownNames::StdOpsFunctionFnOnceCallOnce
    )
}

/// Returns true if the given type is a reference (or raw pointer) to a collection type, in which
/// case the reference/pointer independently tracks the length of the collection, thus effectively
/// tracking a slice of the underlying collection.
pub fn is_slice_pointer<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::RawPtr(target, _) | TyKind::Ref(_, target, _) => {
            // Pointers to sized arrays are thin pointers.
            matches!(target.kind(), TyKind::Slice(..) | TyKind::Str)
        }
        _ => false,
    }
}

/// Returns true if the given type is a reference (or raw pointer) to a dynamic type
pub fn is_dynamic_pointer<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::RawPtr(target, _) | TyKind::Ref(_, target, _) => {
            // Pointers to sized arrays are thin pointers.
            matches!(target.kind(), TyKind::Dynamic(..))
        }
        _ => false,
    }
}

/// Returns true if the given type is a reference (or raw pointer) to a foreign type
pub fn is_foreign_pointer<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::RawPtr(target, _) | TyKind::Ref(_, target, _) => {
            // Pointers to sized arrays are thin pointers.
            matches!(target.kind(), TyKind::Foreign(..))
        }
        _ => false,
    }
}

pub fn is_zst<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    tcx.layout_of(rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map_or(false, |layout| layout.is_zst())
}

pub fn is_transparent_wrapper(ty: Ty) -> bool {
    return if let TyKind::Adt(def, _) = ty.kind() {
        def.repr().transparent()
    } else {
        false
    };
}

pub fn is_manually_drop<'tcx>(ty: Ty<'tcx>) -> bool {
    if let TyKind::Adt(def, _) = ty.kind() {
        def.is_manually_drop()
    } else {
        false
    }
}

/// Returns true if the given type is a reference counting pointer like Rc<T> or Arc<T>.
/// This includes both std::rc::Rc and std::sync::Arc types.
pub fn is_reference_counting_pointer<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => {
            let def_path = tcx.def_path_str(adt_def.did());
            // Check for std::rc::Rc<T>
            if def_path == "std::rc::Rc" || def_path == "alloc::rc::Rc" {
                return true;
            }
            // Check for std::sync::Arc<T>
            if def_path == "std::sync::Arc" || def_path == "alloc::sync::Arc" {
                return true;
            }
            false
        }
        _ => false,
    }
}

pub fn function_return_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    gen_args: GenericArgsRef<'tcx>,
) -> Ty<'tcx> {
    let fn_sig = tcx.fn_sig(def_id);
    let ret_type = fn_sig.skip_binder().output().skip_binder();
    specialize_generic_args(tcx, ret_type, gen_args)
}

pub fn closure_return_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: DefId,
    gen_args: GenericArgsRef<'tcx>,
) -> Ty<'tcx> {
    let fn_sig = gen_args.as_closure().sig();
    let ret_type = fn_sig.skip_binder().output();
    specialize_generic_args(tcx, ret_type, gen_args)
}

/// Closures bring enclosed variables with them that are effectively additional parameters.
/// There is no convenient way to look up their types later on. I.e. unlike ordinary parameters
/// whose types can be looked up in mir.local_decls, these extra parameters need their
/// types extracted from the closure type definitions via the tricky logic below.
pub fn closure_field_types<'tcx>(ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Closure(_, args) => {
            return args
                .as_closure()
                .upvar_tys()
                .iter()
                .collect::<Vec<Ty<'tcx>>>();
        }
        TyKind::Coroutine(_, args) => {
            return args
                .as_coroutine()
                .upvar_tys()
                .iter()
                .collect::<Vec<Ty<'tcx>>>();
        }
        _ => {
            unreachable!("unexpected type {:?}", ty);
        }
    }
}

/// Returns true if the two given types are equal after erasing regions
/// Compare base types directly, ignoring generic arguments
pub fn equal_types<'tcx>(tcx: TyCtxt<'tcx>, ty1: Ty<'tcx>, ty2: Ty<'tcx>) -> bool {
    let ty1 = tcx.erase_and_anonymize_regions(ty1);
    let ty2 = tcx.erase_and_anonymize_regions(ty2);
    if std::mem::discriminant(ty1.kind()) != std::mem::discriminant(ty2.kind()) {
        return false;
    }
    // As we may infer the generic arguments incorrectly, we simply ignore them
    // when comparing the types.
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Adt(def1, _), TyKind::Adt(def2, _)) => def1 == def2,
        (TyKind::Array(elem_ty1, _), TyKind::Array(elem_ty2, _))
        | (TyKind::Slice(elem_ty1), TyKind::Slice(elem_ty2)) => {
            equal_types(tcx, *elem_ty1, *elem_ty2)
        }
        (TyKind::RawPtr(ty1, _), TyKind::RawPtr(ty2, _))
        | (TyKind::Ref(_, ty1, _), TyKind::Ref(_, ty2, _)) => equal_types(tcx, *ty1, *ty2),
        (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|(t1, t2)| equal_types(tcx, t1, t2))
        }
        (TyKind::FnDef(def1, _), TyKind::FnDef(def2, _)) => def1 == def2,
        (TyKind::Closure(def1, _), TyKind::Closure(def2, _))
        | (TyKind::Coroutine(def1, _), TyKind::Coroutine(def2, _))
        | (TyKind::CoroutineClosure(def1, _), TyKind::CoroutineClosure(def2, _))
        | (TyKind::CoroutineWitness(def1, _), TyKind::CoroutineWitness(def2, _)) => def1 == def2,
        (TyKind::Dynamic(..), TyKind::Dynamic(..)) => {
            strip_auto_traits(tcx, ty1) == strip_auto_traits(tcx, ty2)
        }
        _ => ty1 == ty2,
    }
}

/// Returns true if the given two pointer types are compatible.
/// We suppose that a reference type and a mut/const raw pointer type are compatible if
/// their dereference types are compatible.  
/// Pointers of compatible types can point to the same object.
pub fn compatible_pointer_types<'tcx>(tcx: TyCtxt<'tcx>, ty1: Ty<'tcx>, ty2: Ty<'tcx>) -> bool {
    if !ty1.is_any_ptr() || !ty2.is_any_ptr() {
        return false;
    }
    if is_foreign_pointer(ty1) || is_foreign_pointer(ty2) {
        return true;
    }
    // Note: Despite that a function pointer and a function's reference both point to function
    // items, they are not equivalent and they cannot be cast to each other.
    // For example,
    // ```
    // let f = foo;  // f: fn() {foo}
    // let p = &f;   // p: &fn() {foo}
    // let fp: fn() = unsafe { std::mem::transmute(p) };
    // fp();         // Segmentation fault
    // ```
    // If we cast a function's reference into a function pointer and call via the function pointer,
    // it will lead to a segmentation fault.
    // The equivalence between two function pointers are determined by comparing their signatures.
    if ty1.is_fn_ptr() && ty2.is_fn_ptr() {
        let fn_sig1 = ty1.fn_sig(tcx);
        let fn_sig2 = ty2.fn_sig(tcx);
        return fn_sig1.inputs_and_output() == fn_sig2.inputs_and_output();
    }
    let deref_ty1 = get_dereferenced_type(ty1);
    let deref_ty2 = get_dereferenced_type(ty2);
    if !deref_ty1.is_any_ptr() || !deref_ty2.is_any_ptr() {
        // We don't make cast or do type filtering when we propagate the points-to set to a dyn trait
        // pointer, therefore we treat a pointer and a dyn trait pointer as equilvalent pointers.
        if deref_ty1.is_trait() || deref_ty2.is_trait() {
            // TODO: check the implementation relationship between the two types.
            return true;
        } else {
            return equal_types(tcx, deref_ty1, deref_ty2);
        }
    } else {
        return compatible_pointer_types(tcx, deref_ty1, deref_ty2);
    }
}

pub fn matched_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_sig1: FnSigTys<TyCtxt<'tcx>>,
    fn_sig2: FnSigTys<TyCtxt<'tcx>>,
) -> bool {
    let inputs_and_output1 = fn_sig1.inputs_and_output;
    let inputs_and_output2 = fn_sig2.inputs_and_output;
    if inputs_and_output1.len() != inputs_and_output2.len() {
        return false;
    }
    for i in 0..inputs_and_output1.len() {
        let ty1 = inputs_and_output1[i];
        let ty2 = inputs_and_output2[i];
        if ty1.is_any_ptr() && ty2.is_any_ptr() {
            // continue;
            if compatible_pointer_types(tcx, ty1, ty2) {
                continue;
            } else if is_foreign_pointer(ty1) || is_foreign_pointer(ty2) {
                continue;
            }
        }
        if matches!(ty1.kind(), TyKind::Foreign(..)) || matches!(ty2.kind(), TyKind::Foreign(..)) {
            continue;
        }
        if matches!(ty1.kind(), TyKind::Alias(..)) || matches!(ty2.kind(), TyKind::Alias(..)) {
            continue;
        }
        if !equal_types(tcx, ty1, ty2) {
            return false;
        }
    }
    return true;
}

// Given a dynamic type like "dyn Trait + Send", return the dynamic type "dyn Trait"
pub fn strip_auto_traits<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    if let TyKind::Dynamic(predicates, region) = ty.kind() {
        let new_predicates = predicates.iter().filter(
            |bound_pred: &rustc_middle::ty::Binder<'_, ExistentialPredicate<'tcx>>| match bound_pred
                .skip_binder()
            {
                ExistentialPredicate::AutoTrait(_) => false,
                _ => true,
            },
        );
        Ty::new_dynamic(
            tcx,
            tcx.mk_poly_existential_predicates_from_iter(new_predicates),
            *region,
        )
    } else {
        ty
    }
}


/// Returns true if the type (or any type nested within its generic args
/// or field types) contains a `TyKind::Alias` projection (e.g., `<A as Trait>::Assoc`).
/// These projections cause ICEs in rustc's drop shim generator because
/// it cannot normalize them without knowing the concrete impl.
///
/// Other non-concrete types (Param, Dynamic, etc.) are handled fine by rustc.
pub fn contains_alias_projection<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    use std::collections::HashSet;
    fn check<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        visited: &mut HashSet<DefId>,
    ) -> bool {
        match ty.kind() {
            TyKind::Alias(..) => true,
            TyKind::Adt(adt_def, gen_args) => {
                // Check generic args first (fast path)
                if check_generic_args(tcx, gen_args, visited) {
                    return true;
                }
                // Check field types for aliases introduced by associated types
                // (e.g., struct NestedAssoc<A: Trait> { inner: Box<A::Assoc> })
                // Use visited set to prevent infinite recursion on self-referential types
                if !visited.insert(adt_def.did()) {
                    return false;
                }
                adt_def.all_fields().any(|field| {
                    let field_ty = tcx.type_of(field.did).instantiate(tcx, gen_args);
                    check(tcx, field_ty, visited)
                })
            }
            TyKind::Closure(_, gen_args)
            | TyKind::FnDef(_, gen_args)
            | TyKind::Coroutine(_, gen_args)
            | TyKind::CoroutineWitness(_, gen_args) => check_generic_args(tcx, gen_args, visited),
            TyKind::Tuple(types) => types.iter().any(|t| check(tcx, t, visited)),
            TyKind::Ref(_, ty, _) => check(tcx, *ty, visited),
            TyKind::Slice(ty) | TyKind::Array(ty, _) => check(tcx, *ty, visited),
            TyKind::RawPtr(ty, _) => check(tcx, *ty, visited),
            _ => false,
        }
    }

    fn check_generic_args<'tcx>(
        tcx: TyCtxt<'tcx>,
        gen_args: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
        visited: &mut HashSet<DefId>,
    ) -> bool {
        gen_args.iter().any(|arg| {
            if let rustc_middle::ty::GenericArgKind::Type(t) = arg.kind() {
                check(tcx, t, visited)
            } else {
                false
            }
        })
    }

    let mut visited = HashSet::new();
    check(tcx, ty, &mut visited)
}


/// Recursively replace alias types and generic parameters in generic arguments with unit types
/// This helps avoid normalization errors when looking up Drop implementations
fn normalize_ty_for_drop<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Alias(..) => {
            // Replace any alias type with unit type ()
            tcx.types.unit
        }
        TyKind::Param(..) => {
            // Replace generic type parameters with unit type () 
            // This allows resolving Drop impls for generic types like Vec<T>
            tcx.types.unit
        }
        TyKind::Adt(adt_def, args) => {
            // Recursively process generic arguments
            let new_args = tcx.mk_args_from_iter(args.iter().map(|arg| {
                match arg.kind() {
                    GenericArgKind::Type(ty) => normalize_ty_for_drop(tcx, ty).into(),
                    _ => arg, // Keep lifetime and const arguments as-is
                }
            }));
            Ty::new_adt(tcx, *adt_def, new_args)
        }
        TyKind::Array(elem_ty, len) => {
            let new_elem_ty = normalize_ty_for_drop(tcx, *elem_ty);
            Ty::new_array_with_const_len(tcx, new_elem_ty, *len)
        }
        TyKind::Slice(elem_ty) => {
            let new_elem_ty = normalize_ty_for_drop(tcx, *elem_ty);
            Ty::new_slice(tcx, new_elem_ty)
        }
        TyKind::Tuple(types) => {
            let new_types = types.iter().map(|ty| normalize_ty_for_drop(tcx, ty));
            Ty::new_tup_from_iter(tcx, new_types)
        }
        TyKind::Ref(region, ty, mutbl) => {
            let new_ty = normalize_ty_for_drop(tcx, *ty);
            Ty::new_ref(tcx, *region, new_ty, *mutbl)
        }
        TyKind::RawPtr(ty, mutbl) => {
            let new_ty = normalize_ty_for_drop(tcx, *ty);
            Ty::new_ptr(tcx, new_ty, *mutbl)
        }
        // For other types, return as-is since we're only handling the safe subset
        _ => ty,
    }
}

/// Find the Drop trait implementation for a type
pub fn find_drop_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    // Get the Drop trait def_id
    let drop_trait = tcx.lang_items().drop_trait()?;

    // Get the drop method's def_id from the trait's associated items
    let drop_method = tcx
        .associated_items(drop_trait)
        .in_definition_order()
        .find(|item| item.name() == rustc_span::sym::drop)?
        .def_id;

    // Find all implementations of Drop for this type
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();

    // try_resolve may raises an internal compiler error if the type is not normalized
    if !matches!(
        ty.kind(),
        TyKind::Adt(..) | TyKind::Array(..) | TyKind::Slice(..) | TyKind::Tuple(..)
    ) {
        return None;
    }

    // Replace alias types in generic arguments with unit types to avoid normalization errors
    let normalized_ty = normalize_ty_for_drop(tcx, ty);

    // If the type still has unresolved params (e.g., const generic params like N in [u8; N]),
    // we cannot resolve the drop impl. Attempting to do so can panic inside rustc's query
    // system (codegen_select_candidate), and catch_unwind leaves the query in an active state,
    // causing a later assertion failure in incremental cache serialization.
    if normalized_ty.has_param() {
        return None;
    }

    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if let Ok(Some(instance)) = rustc_middle::ty::Instance::try_resolve(
            tcx,
            typing_env,
            drop_method,
            tcx.mk_args(&[normalized_ty.into()]),
        ) {
            Some((instance.def.def_id(), instance.args))
        } else {
            None
        }
    })).unwrap_or(None)
}

pub fn is_drop_impl<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    // Check if this is a method in an impl block
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let rustc_middle::ty::AssocContainer::TraitImpl(_) = assoc_item.container {
            // Check if this impl block implements the Drop trait
            if let Some(trait_ref) = tcx.impl_opt_trait_ref(tcx.parent(def_id)) {
                let trait_ref = trait_ref.skip_binder();
                // Get the Drop trait def_id
                if let Some(drop_trait) = tcx.lang_items().drop_trait() {
                    // Check if this impl is for the Drop trait
                    if trait_ref.def_id == drop_trait {
                        return true;
                    }
                }
            }
        }
    }
    false
}
