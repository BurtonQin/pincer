use rustc_borrowck::consumers::{self, BodyWithBorrowckFacts, ConsumerOptions};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use crate::util::cache::Cache;

/// You must use this function in [`rustc_driver::Callbacks::config`] to call [`get_body_with_borrowck_facts`].
pub fn override_queries(_session: &rustc_session::Session, _local: &mut rustc_middle::util::Providers) {
}

thread_local! {
    static MIR_BODIES: Cache<LocalDefId, BodyWithBorrowckFacts<'static>> = Cache::default();
}

fn fetch_body_with_borrowck_facts(tcx: TyCtxt<'_>, def_id: LocalDefId) -> BodyWithBorrowckFacts<'static> {
    let mut bodies = consumers::get_bodies_with_borrowck_facts(
        tcx,
        def_id,
        ConsumerOptions::PoloniusInputFacts,
    );
    let body_with_facts = bodies.remove(&def_id).unwrap_or_else(|| {
        panic!("borrowck facts not found for {def_id:?}")
    });
    // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
    unsafe { std::mem::transmute(body_with_facts) }
}

/// Gets the MIR body and [Polonius](https://github.com/rust-lang/polonius)-generated
/// [borrowck facts](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_borrowck/struct.BodyWithBorrowckFacts.html)
/// for a given [`LocalDefId`].
///
/// For this function to work, you MUST add [`override_queries`] to the
/// [`rustc_interface::Config`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_interface/interface/struct.Config.html)
/// inside of your [`rustc_driver::Callbacks`]. For example, see
/// [example.rs](https://github.com/willcrichton/flowistry/tree/master/crates/flowistry/examples/example.rs).
///
/// Note that as of May 2022, Polonius can be *very* slow for large functions.
/// It may take up to 30 seconds to analyze a single body with a large CFG.
#[allow(clippy::needless_lifetimes)]
pub fn get_body_with_borrowck_facts(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> &BodyWithBorrowckFacts<'_> {
    MIR_BODIES.with(|cache| {
        let body = cache.get(&def_id, |_| fetch_body_with_borrowck_facts(tcx, def_id));
        unsafe {
            std::mem::transmute::<&BodyWithBorrowckFacts<'static>, &BodyWithBorrowckFacts<'_>>(body)
        }
    })
}

