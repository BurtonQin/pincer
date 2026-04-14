use anyhow::Result;

use rustc_middle::mir::pretty::{write_mir_fn, PrettyPrintMirOptions};
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;

/// Extension trait for [`Body`].
pub trait BodyExt<'tcx> {
    /// Converts a Body to a debug representation.
    fn to_string(&self, tcx: TyCtxt<'tcx>) -> Result<String>;
}

impl<'tcx> BodyExt<'tcx> for Body<'tcx> {
    fn to_string(&self, tcx: TyCtxt<'tcx>) -> Result<String> {
        let mut buffer = Vec::new();
        write_mir_fn(
            tcx,
            self,
            &mut |_, _| Ok(()),
            &mut buffer,
            PrettyPrintMirOptions {
                include_extra_comments: false,
            },
        )?;
        Ok(String::from_utf8(buffer)?)
    }
}
