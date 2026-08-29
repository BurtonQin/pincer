use anyhow::Result;

use rustc_middle::mir::pretty::MirWriter;
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
        MirWriter::new(tcx).write_mir_fn(self, &mut buffer)?;
        Ok(String::from_utf8(buffer)?)
    }
}
