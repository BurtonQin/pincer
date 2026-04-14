use std::collections::{hash_map::DefaultHasher, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use rustc_middle::mir::Place;
use crate::tsa::abstract_value::ConstantValue;
use crate::util::cached_hash::WithCachedHash;

pub trait TypeState: Debug + Copy + Clone + Hash + PartialEq + Eq {
    fn is_error_state(&self) -> bool;
}

pub type SymbState<'tcx, S, P> = Rc<WithCachedHash<SymbolicState<'tcx, S, P>>>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstantKind<'tcx> {
    ConstantVariable(Place<'tcx>),
    EnumDiscriminant(Place<'tcx>),
}

impl<'tcx> std::fmt::Debug for ConstantKind<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantKind::ConstantVariable(place) => write!(f, "const({:?})", place),
            ConstantKind::EnumDiscriminant(place) => write!(f, "discr({:?})", place),
        }
    }
}

impl<'tcx> ConstantKind<'tcx> {
    pub fn place(&self) -> &Place<'tcx> {
        match self {
            ConstantKind::ConstantVariable(place) => place,
            ConstantKind::EnumDiscriminant(place) => place,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExecutionState<'tcx, P>
where
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub constants: HashMap<ConstantKind<'tcx>, ConstantValue>,
    pub aliases: HashSet<P>,
}

impl<'tcx, P> Hash for ExecutionState<'tcx, P>
where
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut h = 0;
        for pair in &self.constants {
            // We cannot move the hasher out of the loop, as
            // we have to use a new DefaultHasher for each element.
            let mut hasher = DefaultHasher::new();
            pair.hash(&mut hasher);
            h ^= hasher.finish();
        }

        for elem in &self.aliases {
            let mut hasher = DefaultHasher::new();
            elem.hash(&mut hasher);
            h ^= hasher.finish();
        }

        state.write_u64(h);
    }
}

impl<'tcx, P> ExecutionState<'tcx, P>
where
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub fn init_exec_state(aliases: HashSet<P>) -> Self {
        ExecutionState {
            constants: HashMap::new(),
            aliases,
        }
    }

    pub fn new_exec_state(aliases: HashSet<P>, constants: HashMap<ConstantKind<'tcx>, ConstantValue>) -> Self {
        ExecutionState { aliases, constants }
    }

    pub fn get_constant_value(&self, place: &Place<'tcx>) -> Option<&ConstantValue> {
        self.constants.get(&ConstantKind::ConstantVariable(place.clone()))
    }

    pub fn add_constant_value(&mut self, place: Place<'tcx>, value: ConstantValue) {
        self.constants.insert(ConstantKind::ConstantVariable(place), value);
    }

    pub fn remove_constant_value(&mut self, place: &Place<'tcx>) {
        self.constants.remove(&ConstantKind::ConstantVariable(place.clone()));
    }

    pub fn discriminant(&self, place: &Place<'tcx>) -> Option<&ConstantValue> {
        self.constants.get(&ConstantKind::EnumDiscriminant(place.clone()))
    }

    pub fn set_discriminant(&mut self, place: Place<'tcx>, value: ConstantValue) {
        self.constants.insert(ConstantKind::EnumDiscriminant(place), value);
    }

    pub fn remove_discriminant(&mut self, place: &Place<'tcx>) {
        self.constants.remove(&ConstantKind::EnumDiscriminant(place.clone()));
    }

    pub fn constants(&self) -> &HashMap<ConstantKind<'tcx>, ConstantValue> {
        &self.constants
    }

    pub fn aliases(&self) -> &HashSet<P> {
        &self.aliases
    }

    pub fn add_alias(&mut self, alias: P) {
        self.aliases.insert(alias);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolicState<'tcx, S, P>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub type_state: S,
    pub execution_state: ExecutionState<'tcx, P>,
}

impl<'tcx, S, P> SymbolicState<'tcx, S, P>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub fn new_symb_state(type_state: S, execution_state: ExecutionState<'tcx, P>) -> Self {
        SymbolicState {
            type_state,
            execution_state,
        }
    }

    pub fn get_type_state(&self) -> S {
        self.type_state
    }

    pub fn set_type_state(&mut self, type_state: S) {
        self.type_state = type_state;
    }

    pub fn get_execution_state(&self) -> &ExecutionState<'tcx, P> {
        &self.execution_state
    }

    pub fn get_constant_value(&self, place: &Place<'tcx>) -> Option<&ConstantValue> {
        self.execution_state.get_constant_value(place)
    }

    pub fn discriminant(&self, place: &Place<'tcx>) -> Option<&ConstantValue> {
        self.execution_state.discriminant(place)
    }

    pub fn constants(&self) -> &HashMap<ConstantKind<'tcx>, ConstantValue> {
        self.execution_state.constants()
    }

    pub fn aliases(&self) -> &HashSet<P> {
        self.execution_state.aliases()
    }

    pub fn constants_mut(&mut self) -> &mut HashMap<ConstantKind<'tcx>, ConstantValue> {
        &mut self.execution_state.constants
    }

    pub fn aliases_mut(&mut self) -> &mut HashSet<P> {
        &mut self.execution_state.aliases
    }

    pub fn add_constant_value(&mut self, place: Place<'tcx>, value: ConstantValue) {
        self.execution_state.add_constant_value(place, value);
    }

    pub fn remove_constant_value(&mut self, place: &Place<'tcx>) {
        self.execution_state.remove_constant_value(place);
    }

    pub fn set_discriminant(&mut self, place: Place<'tcx>, value: ConstantValue) {
        self.execution_state.set_discriminant(place, value);
    }

    pub fn remove_discriminant(&mut self, place: &Place<'tcx>) {
        self.execution_state.remove_discriminant(place);
    }

    pub fn add_alias(&mut self, alias: P) {
        self.execution_state.add_alias(alias);
    }
}

pub trait SymbStateSupport <'tcx, S, P>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    fn new_symb_state(type_state: S, execution_state: ExecutionState<'tcx, P>) -> Self;
    fn clone_owned(&self) -> Self;
    fn borrow_mut(&mut self) -> &mut WithCachedHash<SymbolicState<'tcx, S, P>>;
}

impl<'tcx, S, P> SymbStateSupport<'tcx, S, P> for SymbState<'tcx, S, P>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    fn new_symb_state(type_state: S, execution_state: ExecutionState<'tcx, P>) -> Self {
        Rc::new(
            WithCachedHash::new(
                SymbolicState::new_symb_state(type_state, execution_state)
            )
        )
    }

    fn clone_owned(&self) -> Self {
        Rc::new((**self).clone())
    }

    /// Returns a mutable reference into the given Rc. 
    /// Panics if there are other Rc or Weak pointers to the same allocation.
    fn borrow_mut(&mut self) -> &mut WithCachedHash<SymbolicState<'tcx, S, P>> {
        Rc::get_mut(self).unwrap()
    }
}

impl<'tcx, S, P> std::fmt::Debug for WithCachedHash<SymbolicState<'tcx, S, P>>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<{:?}, {:?}, {:?}>",
            self.type_state,
            self.execution_state.aliases(),
            self.execution_state.constants()
        )
    }
}
