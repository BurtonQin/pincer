// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.


use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgKind, GenericArgsRef};
use rustc_middle::ty::Const;

/// Information that identifies a function instance.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct FuncDef<'tcx> {
    /// The crate specific key that is used to identify the function in the current crate.
    pub def_id: DefId,

    /// The generic argument types with which the referenced function was instantiated, if generic.
    pub generic_args: GenericArgsRef<'tcx>,
}

impl<'tcx> FuncDef<'tcx> {
    pub fn new_func_def(
        def_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
    ) -> FuncDef<'tcx> {
        FuncDef { def_id, generic_args }
    }
}

impl<'tcx> ToString for FuncDef<'tcx> {
    fn to_string(&self) -> String {
        let const_to_str = |c: &Const| -> String {
            if let Some(v) = c.try_to_scalar() {
                return v.to_string();
            }
            return "_".to_string();
        };

        let tmp1 = format!("{:?}", self.def_id);
        let crate_name = &tmp1[tmp1.find("~ ").unwrap() + 2..tmp1.find("[").unwrap()];
        let tmp2 = &tmp1[tmp1.find("::").unwrap() + 2..tmp1.len() - 1];
        let mut tmp3 = "".to_string();
        if !self.generic_args.is_empty() {
            tmp3.push('<');
            let tys = self
                .generic_args
                .iter()
                .filter_map(|gen_arg| match &gen_arg.kind() {
                    GenericArgKind::Type(ty) => Some(format!("{:?}", ty)),
                    GenericArgKind::Const(c) => Some(const_to_str(c)),
                    _ => None,
                })
                .collect::<Vec<String>>();
            tmp3.push_str(&tys.join(", "));
            tmp3.push('>');
        }
        format!("{}::{}{}", crate_name, tmp2, tmp3)
    }
}
