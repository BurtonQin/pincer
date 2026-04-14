use rustc_middle::ty::TyCtxt;
use rustc_data_structures::fx::FxHashMap;
use std::hash::Hash;
use std::sync::RwLock;

pub struct SliceInterner<'tcx, T> {
    map: RwLock<FxHashMap<Vec<T>, &'tcx [T]>>,
}

impl<'tcx, T> SliceInterner<'tcx, T>
where
    T: Eq + Hash + Copy,
{
    pub fn new() -> Self {
        Self {
            map: RwLock::new(FxHashMap::default()),
        }
    }

    /// Interns a slice and returns a reference to the interned slice.
    pub fn intern(&self, tcx: TyCtxt<'tcx>, slice: &[T]) -> &'tcx [T] {
        // Check if the slice is already interned.
        if let Some(interned) = self.get(slice) {
            return interned;
        }

        // If not, allocate the slice in the arena and insert it into the map.
        let mut map = self.map.write().unwrap();
        let interned = tcx.arena.alloc_slice(slice);
        map.insert(slice.to_vec(), interned);
        interned
    }

    /// Get an interned reference out of this interner.
    pub fn get(&self, slice: &[T]) -> Option<&'tcx [T]> {
        self.map
            .read()
            .expect("interner lock should not be poisoned")
            .get(slice)
            .copied()
    }
}