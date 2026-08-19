Verus AI verification history snapshot
======================================

GitHub rejects files larger than 100 MiB, so the two largest archives are
stored as ordered 45 MiB parts.

Reassemble them from this directory:

  cat argus-project-37bc66d4d753.tar.zst.*.part \
    > argus-project-37bc66d4d753.tar.zst

  cat verus-ai-source.tar.zst.*.part \
    > verus-ai-source.tar.zst

Verify every stored file:

  sha256sum -c SHA256SUMS

After reassembly, verify the logical/original archives:

  sha256sum -c ORIGINAL_SHA256SUMS

Test or list an archive without extracting it:

  zstd -t argus-project-37bc66d4d753.tar.zst
  tar --zstd -tf argus-project-37bc66d4d753.tar.zst

Contents
--------

argus-project-37bc66d4d753.tar.zst.*.part
  Complete Argus lifecycle directory. It includes agent_io.jsonl,
  events.jsonl, inbox/backlog/usage logs, daemon state, and all handoffs.

verification-process.tar.zst
  MISSION.md, research/, .verus_agent/, and tools/operator/ from the project.

verus-ai-source.tar.zst.*.part
  The verus-ai harness source snapshot, excluding .git and .venv.

verified-memory-allocator-working-tree.patch.zst
verified-memory-allocator-status.txt.zst
verus-ai-working-tree.patch.zst
  Git state needed to reconstruct the exact uncommitted source state.

argus-file-manifest.tsv.zst
  Per-file path, byte size, and modification time for the Argus directory.

SNAPSHOT_METADATA.tsv
  Snapshot time, repository revisions, source byte count, and file count.

ORIGINAL_SHA256SUMS
  Checksums of the logical archives before the large ones were split.

SHA256SUMS
  Checksums of the files as stored in Git.
