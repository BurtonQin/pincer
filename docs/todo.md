# TODO List

## Backward Solver
- Duplicate flow origins computed for `test_interprocedural_indirect_reference` in `bw_flow_tests`

## AXM Check
- Determine whether an alias is a pointer escaped from a raw pointer. Currently, the AXM compliance check does not account for this, causing false positives when a raw pointer is created but not escaped (see `safe_raw_ptr_not_escaped` in `modularity_tests`)

## Global Pointers
- Support analysis of global raw pointers (see `global_ptr_test` in `use_after_free_tests`)
