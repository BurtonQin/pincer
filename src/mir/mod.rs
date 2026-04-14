// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

pub mod body_ext;
pub mod borrowck_facts;
pub mod builtins;
pub mod drop_shim;
pub mod function;
pub mod known_names;
pub mod place_ext;
pub mod projection;
pub mod raw_ptr;
pub mod reference_set;
pub mod unit;

pub use unit::{ContainingFunction, StatementOrTerminator, Unit};
pub use function::FuncDef;
pub use drop_shim::DropShim;

