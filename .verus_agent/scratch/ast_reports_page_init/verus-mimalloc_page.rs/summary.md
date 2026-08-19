# AST Consistency Report: ast_orig_pq21fq8u

**Source:** `/tmp/ast_orig_pq21fq8u.rs`
**Verus:** `verus-mimalloc/page.rs`

## Summary

- Functions matched: 12/13
- Functions mismatched: 1
- Missing in Verus: 0
- Extra in Verus: 0
- **Consistent: NO**

## Inconsistent Functions

| Function | Status | Source Lines | Verus Lines |
|----------|--------|-------------|-------------|
| `page_init` [page_init.diff](full/page_init.diff) [src](full/page_init_source.rs) [verus](full/page_init_verus.rs) | MISMATCH | 151-236 | 162-605 |

## Full Diffs (source vs Verus with spec/proof)

Directory: `full/`

| Function | Status | Files |
|----------|--------|-------|
| `page_init` | MISMATCH | page_init_source.rs, page_init_verus.rs, page_init.diff |

## Exec-Only Diffs (source vs Verus stripped of ghost/proof)

Directory: `exec-only/`

These diffs show only the executable code differences, with all Verus
annotations (requires/ensures, proof blocks, ghost variables, invariants)
removed. This makes it easier to spot real exec logic changes.

| Function | Status | Files |
|----------|--------|-------|
| `page_init` | MISMATCH | page_init_source_stripped.rs, page_init_verus_stripped.rs, page_init.diff |

## All Functions

| Function | Status | Hash Match | Verification |
|----------|--------|------------|--------------|
| `find_free_page` | MATCH | ✅ |  |
| `find_page` | MATCH | ✅ |  |
| `page_free` | MATCH | ✅ |  |
| `page_fresh` | MATCH | ✅ |  |
| `page_fresh_alloc` | MATCH | ✅ |  |
| `page_init` | MISMATCH | ❌ |  |
| `page_queue_enqueue_from` | MATCH | ✅ |  |
| `page_queue_find_free_ex` | MATCH | ✅ |  |
| `page_queue_of` | MATCH | ✅ |  |
| `page_retire` | MATCH | ✅ |  |
| `page_to_full` | MATCH | ✅ |  |
| `page_try_use_delayed_free` | MATCH | ✅ |  |
| `page_unfull` | MATCH | ✅ |  |

