# AST Consistency Report: ast_orig_454zez_n

**Source:** `/tmp/ast_orig_454zez_n.rs`
**Verus:** `verus-mimalloc/alloc_generic.rs`

## Summary

- Functions matched: 5/6
- Functions mismatched: 1
- Missing in Verus: 0
- Extra in Verus: 0
- **Consistent: NO**

## Inconsistent Functions

| Function | Status | Source Lines | Verus Lines |
|----------|--------|-------------|-------------|
| `heap_delayed_free_partial` [heap_delayed_free_partial.diff](full/heap_delayed_free_partial.diff) [src](full/heap_delayed_free_partial_source.rs) [verus](full/heap_delayed_free_partial_verus.rs) | MISMATCH | 240-272 | 1093-1178 |

## Full Diffs (source vs Verus with spec/proof)

Directory: `full/`

| Function | Status | Files |
|----------|--------|-------|
| `heap_delayed_free_partial` | MISMATCH | heap_delayed_free_partial_source.rs, heap_delayed_free_partial_verus.rs, heap_delayed_free_partial.diff |

## Exec-Only Diffs (source vs Verus stripped of ghost/proof)

Directory: `exec-only/`

These diffs show only the executable code differences, with all Verus
annotations (requires/ensures, proof blocks, ghost variables, invariants)
removed. This makes it easier to spot real exec logic changes.

| Function | Status | Files |
|----------|--------|-------|
| `heap_delayed_free_partial` | MISMATCH | heap_delayed_free_partial_source_stripped.rs, heap_delayed_free_partial_verus_stripped.rs, heap_delayed_free_partial.diff |

## All Functions

| Function | Status | Hash Match | Verification |
|----------|--------|------------|--------------|
| `heap_delayed_free_partial` | MISMATCH | ❌ |  |
| `malloc_generic` | MATCH | ✅ |  |
| `page_extend_free` | MATCH | ✅ |  |
| `page_free_collect` | MATCH | ✅ |  |
| `page_free_list_extend` | MATCH | ✅ |  |
| `page_thread_free_collect` | MATCH | ✅ |  |

