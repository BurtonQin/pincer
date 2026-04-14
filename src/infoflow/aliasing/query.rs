use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::infoflow::AccessPath;
use crate::infoflow::PointerFlowOrigin;
use crate::infoflow::Unit;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Query<'tcx> {
    pub access_path: AccessPath<'tcx>,
    pub unit: Unit<'tcx>,
}

#[derive(Debug, Default)]
pub struct QueryResult<'tcx> {
    pub flow_origins: HashSet<PointerFlowOrigin<'tcx>>,
    pub aliases: HashSet<AccessPath<'tcx>>,
    pub finished: bool,
}

pub struct QueryCache<'tcx> {
    cache: RefCell<HashMap<Query<'tcx>, QueryResult<'tcx>>>,
}

#[derive(Clone)]
pub struct QueryList<'tcx> {
    queries: Rc<RefCell<Vec<Query<'tcx>>>>,
}

impl<'tcx> QueryList<'tcx> {
    pub fn new() -> QueryList<'tcx> {
        QueryList {
            queries: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn add_query(&self, query: Query<'tcx>) {
        self.queries.borrow_mut().push(query);
    }

    pub fn pop(&self) -> Option<Query<'tcx>> {
        self.queries.borrow_mut().pop()
    }

    pub fn curr_query(&self) -> Query<'tcx> {
        self.queries.borrow().last().unwrap().clone()
    }
}

impl<'tcx> Query<'tcx> {
    pub fn new(access_path: AccessPath<'tcx>, unit: Unit<'tcx>) -> Query<'tcx> {
        Query { access_path, unit }
    }
}

impl<'tcx> QueryResult<'tcx> {
    pub fn new() -> QueryResult<'tcx> {
        QueryResult {
            flow_origins: HashSet::new(),
            aliases: HashSet::new(),
            finished: false,
        }
    }

    pub fn add_flow_origin(&mut self, flow_origin: PointerFlowOrigin<'tcx>) {
        self.flow_origins.insert(flow_origin);
    }

    pub fn add_alias(&mut self, alias: AccessPath<'tcx>) {
        self.aliases.insert(alias);
    }

    pub fn add_aliases(&mut self, aliases: &HashSet<AccessPath<'tcx>>) {
        self.aliases.extend(aliases);
    }
}

impl<'tcx> QueryCache<'tcx> {
    pub fn new() -> QueryCache<'tcx> {
        QueryCache {
            cache: RefCell::new(HashMap::new()),
        }
    }

    pub fn add_query(&self, query: Query<'tcx>) {
        self.cache.borrow_mut().insert(query, QueryResult::new());
    }

    pub fn has_query(&self, query: &Query<'tcx>) -> bool {
        self.cache.borrow().contains_key(query)
    }

    pub fn is_query_finished(&self, query: &Query<'tcx>) -> bool {
        self.cache
            .borrow()
            .get(query)
            .map_or(false, |r| r.finished)
    }

    pub fn mark_query_finished(&self, query: &Query<'tcx>) {
        if let Some(result) = self.cache.borrow_mut().get_mut(query) {
            result.finished = true;
        } else {
            panic!("Query {:?} not found in cache", query);
        }
    }

    pub fn insert(&self, query: Query<'tcx>, query_result: QueryResult<'tcx>) {
        self.cache.borrow_mut().insert(query, query_result);
    }

    pub fn add_flow_origin(&self, query: Query<'tcx>, flow_origin: PointerFlowOrigin<'tcx>) {
        let mut cache = self.cache.borrow_mut();
        let query_result = cache.entry(query).or_default();
        query_result.add_flow_origin(flow_origin);
    }

    pub fn add_alias(&self, query: Query<'tcx>, alias: AccessPath<'tcx>) {
        let mut cache = self.cache.borrow_mut();
        let query_result = cache.entry(query).or_default();
        query_result.add_alias(alias);
    }

    pub fn add_aliases(&self, query: Query<'tcx>, aliases: &HashSet<AccessPath<'tcx>>) {
        let mut cache = self.cache.borrow_mut();
        let query_result = cache.entry(query).or_default();
        query_result.add_aliases(aliases);
    }

    pub fn get_query_result(&self, query: &Query<'tcx>) -> Ref<QueryResult<'tcx>> {
        Ref::map(self.cache.borrow(), |map: &_| map.get(query).unwrap())
    }

    pub fn get_flow_origins(&self, query: &Query<'tcx>) -> HashSet<PointerFlowOrigin<'tcx>> {
        self.cache
            .borrow()
            .get(query)
            .map(|result| result.flow_origins.clone())
            .unwrap_or_default()
    }

    pub fn get_aliases(&self, query: &Query<'tcx>) -> HashSet<AccessPath<'tcx>> {
        self.cache
            .borrow()
            .get(query)
            .map(|result| result.aliases.clone())
            .unwrap_or_default()
    }
}
