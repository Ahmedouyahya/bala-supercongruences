#!/usr/bin/env bash
# Collects the Lean sources of all checks in this folder into one tree, as they were laid out on the
# machine where the checks ran:
#   <out>/BalaCheck/    -> the BalaCheck library of the Formal Conjectures workspace (fc-ws)
#   <out>/Submission/   -> the Submission library of the Comparator workspace (cmp-ws)
#   <out>/run/, <out>/challenges/ -> Comparator configurations and the official challenge files
# A file that occurs in several entry folders must be identical in all of them; otherwise the script stops.
# Usage: assemble-workspaces.sh <out>   (see PROTOCOL.md for the rest of the set-up)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: assemble-workspaces.sh <output folder>}
mkdir -p "$out"/BalaCheck "$out"/Submission "$out"/run "$out"/challenges
n=0
for entry in "$here"/*/; do
  for pair in "fc-workspace/BalaCheck:BalaCheck" "comparator-workspace/Submission:Submission" \
              "comparator-workspace/run:run" "comparator-workspace/challenges:challenges"; do
    src="$entry${pair%%:*}"; dst="$out/${pair##*:}"
    [ -d "$src" ] || continue
    while IFS= read -r -d '' f; do
      rel=${f#"$src"/}; t="$dst/$rel"; mkdir -p "$(dirname "$t")"
      if [ ! -e "$t" ]; then
        cp -p "$f" "$t"; n=$((n+1))
      elif [ "$(basename "$f")" = GREP-ALLOW.txt ]; then
        # each entry folder keeps the allow-list as it stood at that check; the union is the final list
        grep -vxF -f "$t" "$f" >> "$t" || true
      else
        cmp -s "$f" "$t" || { echo "conflict: $f differs from an earlier copy of $rel" >&2; exit 1; }
      fi
    done < <(find "$src" -type f -print0 | sort -z)
  done
done
echo "assembled $n files into $out"
