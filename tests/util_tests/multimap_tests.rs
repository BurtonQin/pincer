#[cfg(test)]
mod test {
    use multimap::MultiMap;

    #[test]
    fn test_multimap() {
        let mut map = MultiMap::new();
        map.insert(1, 2);
        map.insert(1, 3);
        assert_eq!(map.get_vec(&1).unwrap(), &vec![2, 3]);

        let mut map2 = MultiMap::new();
        map2.entry(1).or_insert(2);
        map2.entry(1).or_insert(3);
        assert_eq!(map2.get_vec(&1).unwrap(), &vec![2]);
    }
}
