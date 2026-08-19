# AST Consistency Report: ast_orig_uishkdxx

**Source:** `/tmp/ast_orig_uishkdxx.rs`
**Verus:** `verus-mimalloc/linked_list.rs`

## Summary

- Functions matched: 26/27
- Functions mismatched: 1
- Missing in Verus: 0
- Extra in Verus: 2
- **Consistent: NO**

## Inconsistent Functions

| Function | Status | Source Lines | Verus Lines |
|----------|--------|-------------|-------------|
| `LL::set_ghost_data` [LL__set_ghost_data.diff](full/LL__set_ghost_data.diff) [src](full/LL__set_ghost_data_source.rs) [verus](full/LL__set_ghost_data_verus.rs) | MISMATCH | 205-214 | 1616-1661 |
| `LL::empty#2` [verus](full/LL__empty#2_verus.rs) | EXTRA_IN_VERUS |  | 1602-1608 |
| `LL::new#2` [verus](full/LL__new#2_verus.rs) | EXTRA_IN_VERUS |  | 1562-1599 |

## Full Diffs (source vs Verus with spec/proof)

Directory: `full/`

| Function | Status | Files |
|----------|--------|-------|
| `LL::set_ghost_data` | MISMATCH | LL__set_ghost_data_source.rs, LL__set_ghost_data_verus.rs, LL__set_ghost_data.diff |
| `LL::empty#2` | EXTRA_IN_VERUS | LL__empty#2_verus.rs (EXTRA) |
| `LL::new#2` | EXTRA_IN_VERUS | LL__new#2_verus.rs (EXTRA) |

## Exec-Only Diffs (source vs Verus stripped of ghost/proof)

Directory: `exec-only/`

These diffs show only the executable code differences, with all Verus
annotations (requires/ensures, proof blocks, ghost variables, invariants)
removed. This makes it easier to spot real exec logic changes.

| Function | Status | Files |
|----------|--------|-------|
| `LL::set_ghost_data` | MISMATCH | LL__set_ghost_data_source_stripped.rs, LL__set_ghost_data_verus_stripped.rs, LL__set_ghost_data.diff |
| `LL::empty#2` | EXTRA_IN_VERUS | LL__empty#2_verus.rs (EXTRA) |
| `LL::new#2` | EXTRA_IN_VERUS | LL__new#2_verus.rs (EXTRA) |


## Struct Issues

| Struct | Status | Files |
|--------|--------|-------|
| `LL` | MISMATCH | struct_LL_source.rs, struct_LL_verus.rs, struct_LL.diff |
| `LLData` | MISMATCH | struct_LLData_source.rs, struct_LLData_verus.rs, struct_LLData.diff |

## All Functions

| Function | Status | Hash Match | Verification |
|----------|--------|------------|--------------|
| `LL::append` | MATCH | ✅ |  |
| `LL::block_write_ptr` | MATCH | ✅ |  |
| `LL::empty` | MATCH | ✅ |  |
| `LL::insert_block` | MATCH | ✅ |  |
| `LL::is_empty` | MATCH | ✅ |  |
| `LL::make_empty` | MATCH | ✅ |  |
| `LL::new` | MATCH | ✅ |  |
| `LL::pop_block` | MATCH | ✅ |  |
| `LL::prepend_contiguous_blocks` | MATCH | ✅ |  |
| `LL::set_ghost_data` | MISMATCH | ❌ |  |
| `Node::clone` | MATCH | ✅ |  |
| `ThreadLLSimple::atomic_insert_block` | MATCH | ✅ |  |
| `ThreadLLSimple::empty` | MATCH | ✅ |  |
| `ThreadLLSimple::take` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::check_is_good` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::disable` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::empty` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::enable` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::take` | MATCH | ✅ |  |
| `ThreadLLWithDelayBits::try_use_delayed_free` | MATCH | ✅ |  |
| `atomic_yield` | MATCH | ✅ |  |
| `masked_ptr_delay_get_delay` | MATCH | ✅ |  |
| `masked_ptr_delay_get_is_use_delayed` | MATCH | ✅ |  |
| `masked_ptr_delay_get_ptr` | MATCH | ✅ |  |
| `masked_ptr_delay_set_delay` | MATCH | ✅ |  |
| `masked_ptr_delay_set_freeing` | MATCH | ✅ |  |
| `masked_ptr_delay_set_ptr` | MATCH | ✅ |  |
| `LL::empty#2` | EXTRA_IN_VERUS | ❌ |  |
| `LL::new#2` | EXTRA_IN_VERUS | ❌ |  |

## Inconsistent Structs

| Struct | Status | Source Lines | Verus Lines |
|--------|--------|-------------|-------------|
| `LL` | MISMATCH | 64-71 | 134-141 |
| `LLData` | MISMATCH | 54-62 | 122-132 |

