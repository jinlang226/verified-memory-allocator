# AST Consistency Report: ast_orig_flmsiaqi

**Source:** `/tmp/ast_orig_flmsiaqi.rs`
**Verus:** `verus-mimalloc/linked_list.rs`

## Summary

- Functions matched: 25/27
- Functions mismatched: 2
- Missing in Verus: 0
- Extra in Verus: 2
- **Consistent: NO**

## Inconsistent Functions

| Function | Status | Source Lines | Verus Lines |
|----------|--------|-------------|-------------|
| `LL::pop_block` [LL__pop_block.diff](full/LL__pop_block.diff) [src](full/LL__pop_block_source.rs) [verus](full/LL__pop_block_verus.rs) | MISMATCH | 147-161 | 1404-1585 |
| `ThreadLLSimple::take` [ThreadLLSimple__take.diff](full/ThreadLLSimple__take.diff) [src](full/ThreadLLSimple__take_source.rs) [verus](full/ThreadLLSimple__take_verus.rs) | MISMATCH | 528-559 | 2783-2830 |
| `LL::empty#2` [verus](full/LL__empty#2_verus.rs) | EXTRA_IN_VERUS |  | 1818-1824 |
| `LL::new#2` [verus](full/LL__new#2_verus.rs) | EXTRA_IN_VERUS |  | 1778-1815 |

## Full Diffs (source vs Verus with spec/proof)

Directory: `full/`

| Function | Status | Files |
|----------|--------|-------|
| `LL::pop_block` | MISMATCH | LL__pop_block_source.rs, LL__pop_block_verus.rs, LL__pop_block.diff |
| `ThreadLLSimple::take` | MISMATCH | ThreadLLSimple__take_source.rs, ThreadLLSimple__take_verus.rs, ThreadLLSimple__take.diff |
| `LL::empty#2` | EXTRA_IN_VERUS | LL__empty#2_verus.rs (EXTRA) |
| `LL::new#2` | EXTRA_IN_VERUS | LL__new#2_verus.rs (EXTRA) |

## Exec-Only Diffs (source vs Verus stripped of ghost/proof)

Directory: `exec-only/`

These diffs show only the executable code differences, with all Verus
annotations (requires/ensures, proof blocks, ghost variables, invariants)
removed. This makes it easier to spot real exec logic changes.

| Function | Status | Files |
|----------|--------|-------|
| `LL::pop_block` | MISMATCH | LL__pop_block_source_stripped.rs, LL__pop_block_verus_stripped.rs, LL__pop_block.diff |
| `ThreadLLSimple::take` | MISMATCH | ThreadLLSimple__take_source_stripped.rs, ThreadLLSimple__take_verus_stripped.rs, ThreadLLSimple__take.diff |
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
| `LL::pop_block` | MISMATCH | ❌ |  |
| `LL::prepend_contiguous_blocks` | MATCH | ✅ |  |
| `LL::set_ghost_data` | MATCH | ✅ |  |
| `Node::clone` | MATCH | ✅ |  |
| `ThreadLLSimple::atomic_insert_block` | MATCH | ✅ |  |
| `ThreadLLSimple::empty` | MATCH | ✅ |  |
| `ThreadLLSimple::take` | MISMATCH | ❌ |  |
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
| `LL` | MISMATCH | 64-71 | 176-183 |
| `LLData` | MISMATCH | 54-62 | 164-174 |

