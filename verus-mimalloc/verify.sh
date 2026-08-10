#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if [ -z "${VERUS_PATH:-}" ]; then
    VERUS_PATH="verus"
fi

"$VERUS_PATH" --triggers-mode=silent --no-auto-recommends-check --rlimit 100 \
    --extern libc=../build/liblibc.rlib lib.rs "$@" --time -- -Zproc-macro-backtrace
