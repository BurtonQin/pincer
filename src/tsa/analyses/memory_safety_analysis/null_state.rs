use crate::tsa::TypeState;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Default)]
pub enum NullState {
    #[default]
    NonNull,
    Null,
    Error(ErrorKind),
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum ErrorKind {
    DoubleFree,
    UseAfterFree,
    DanglingPointer,
}

impl TypeState for NullState {
    fn is_error_state(&self) -> bool {
        matches!(self, NullState::Error(_))
    }
}

impl NullState {
    pub fn is_null(&self) -> bool {
        matches!(self, NullState::Null)
    }

    pub fn is_non_null(&self) -> bool {
        matches!(self, NullState::NonNull)
    }
}
