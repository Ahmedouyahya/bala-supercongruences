# Statement check for the Lean proofs

Each `Check*.lean` file contains the benchmark statement from `statements/lean-targets/` verbatim, with its original `open` lines, inside its own namespace. The original `sorry` is replaced by a proof that first shows the benchmark definition equals the repository's definition (by `rfl`, by unfolding, or for A370092 by induction) and then applies the repository's theorem. If the repository had changed a definition or weakened a statement, these files would not compile. The first three files (A361711, A364175, A364178) were written by hand, and the benchmark's `a_one`, `a_two` and `a_three` for A364175 (which are `sorry` in the benchmark itself) are omitted there. The other nine files were generated on 2026-10-16 by copying the whole target except the import line; sanity lemmas that are `sorry` in the target itself stay `sorry` (they print a warning but are not used by the conjecture, as `#print axioms` shows). For A370092 the definition of `a` uses well-founded recursion, so the file proves the two copies equal by strong induction before applying the repository's theorem.

Run from `lean/` after building the proof modules (see `lean/README.md`):

```
for f in ../verification/lean-statement-check/Check*.lean; do ~/.elan/bin/lake env lean $f 2>&1 | grep -E 'axioms|error'; done
```

Expected output, one line per file, e.g. `'Bench361711.A361711_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]`. Result on 2026-10-16: all 12 files compile, each printing `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Verbatim check

`verbatim_check.py` (run from the repository root: `python3 -I verification/lean-statement-check/verbatim_check.py`) extracts every definition of each benchmark target, with its docstring, and the docstring and statement of the conjecture, and checks that each occurs character for character in the entry's files in `lean/BalaProofs/`. Output and a control run (a weakened statement and a one-character change to a definition, both reported): `outputs/verbatim-check.txt`. The `Check*.lean` files above check the same thing through Lean; this script checks the text.
