use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::Unit;

pub trait PathEdgeNode: std::cmp::Eq + std::hash::Hash + Copy {}
pub trait PathEdgeData: std::cmp::Eq + std::hash::Hash + Clone {}

/// A path edge as described in the IFDS/IDE algorithms.
///
/// N: The type of nodes in the interprocedural control-flow graph. Typically a statement.
/// D: The type of data-flow facts to be computed by the tabulation problem.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct PathEdge<N, D> {
    source: (N, D),
    target: (N, D),
}

impl<N, D> std::fmt::Debug for PathEdge<N, D>
where
    N: std::fmt::Debug,
    D: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}@{:?} --> {:?}@{:?}",
            self.source.1, self.source.0, self.target.1, self.target.0
        )
    }
}

impl<N, D> PathEdge<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new(start: N, dsource: D, target: N, dtarget: D) -> PathEdge<N, D> {
        PathEdge {
            source: (start, dsource),
            target: (target, dtarget),
        }
    }

    pub fn get_target(&self) -> N {
        self.target.0
    }

    pub fn get_start(&self) -> N {
        self.source.0
    }

    pub fn fact_at_source(&self) -> &D {
        &self.source.1
    }

    pub fn fact_at_target(&self) -> &D {
        &self.target.1
    }

    pub fn get_start_node(&self) -> &(N, D) {
        &self.source
    }

    pub fn get_target_node(&self) -> &(N, D) {
        &self.target
    }
}

impl<'tcx> PathEdgeData for AccessPath<'tcx> {}
impl<'tcx> PathEdgeNode for Unit<'tcx> {}
