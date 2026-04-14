pub trait AbstractValue {
    fn is_top(&self) -> bool;
    fn is_bottom(&self) -> bool;
    fn join_with(&mut self, v: &Self) -> bool;
    fn join(v1: &Self, v2: &Self) -> Self
    where
        Self: Sized + Clone,
    {
        let mut res = v1.clone();
        res.join_with(v2);
        res
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum ConstantValue {
    Top,
    Constant(u32),
    Bottom,
}

impl std::fmt::Debug for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Top => write!(f, "T"),
            ConstantValue::Constant(v) => write!(f, "{}", v),
            ConstantValue::Bottom => write!(f, "⊥"),
        }
    }
}

impl AbstractValue for ConstantValue {
    fn is_top(&self) -> bool {
        matches!(self, ConstantValue::Top)
    }

    fn is_bottom(&self) -> bool {
        matches!(self, ConstantValue::Bottom)
    }

    fn join_with(&mut self, v: &Self) -> bool {
        match self {
            ConstantValue::Top => return false,
            ConstantValue::Bottom => {
                *self = *v;
                !v.is_bottom()
            }
            ConstantValue::Constant(v1) => match v {
                ConstantValue::Top => {
                    *self = ConstantValue::Top;
                    true
                }
                ConstantValue::Constant(v2) => {
                    if v1 == v2 {
                        false
                    } else {
                        *self = ConstantValue::Top;
                        true
                    }
                }
                ConstantValue::Bottom => false,
            },
        }
    }
}
