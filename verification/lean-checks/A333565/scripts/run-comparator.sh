#!/usr/bin/env bash
# usage: run-comparator.sh <config.json relative to cmp-ws> <output file>
L=${BALA_CHECK_DIR:?set BALA_CHECK_DIR to the folder that holds fc-ws, cmp-ws and tools (see PROTOCOL.md)}
cd $L/cmp-ws && export PATH=$L/tools/bin:$L/tools/lean4export/.lake/build/bin:$L/tools/nanoda_lib/target/release:$HOME/.elan/bin:$PATH
systemd-run --user --scope -q -p MemoryMax=6G nice -n 10 lake env $L/tools/comparator/.lake/build/bin/comparator "$1" > "$2" 2>&1
rc=$?; echo "comparator exit=$rc :: $1"; grep -v -E '^warning|^Exporting|^Note|^Hint|^info|^ |^$|^[✔⚠]' "$2" | tail -6 | cut -c1-200; exit $rc
