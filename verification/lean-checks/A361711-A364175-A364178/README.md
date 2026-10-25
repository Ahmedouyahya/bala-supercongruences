# Benchmark-checker runs for A361711, A364175 and A364178

Result: the repository's Lean proofs of A361711, A364175 and A364178 (`lean/BalaProofs/A361711.lean`, `A364175.lean`, `A364178.lean`, Lean v4.35.0) were ported to the benchmark's environment (Lean v4.27.0, Formal Conjectures commit 67338a1) and pass every check there, including the benchmark's checker Comparator with the Lean kernel and the independent nanoda kernel. Checked on 2026-10-16. These three proofs were already compiled, axiom-checked and compared with the targets in the repository's environment before this date; this folder adds the checks of the protocol used for A352275 and A386548.

## How the port was made

- `scripts/port_old.py` generates `fc-workspace/BalaCheck/Old/`: the eleven helper files are copied unchanged except for the import lines; in each main file the copied target definition is removed and the unmodified target module is imported instead, our final theorem keeps its statement and proof under a primed name, and a last theorem `<entry>_from_target : type_of% @<target theorem>` takes its statement from the target module.
- One manual edit was needed for the older Mathlib (`scripts/PORT-LOG.md`): `Finsupp.finsetSum_apply` is called `Finsupp.finset_sum_apply` there.
- `scripts/port_cmp.py` generates `comparator-workspace/Submission/`: the repository proof file with the definition verbatim (`<entry>Full.lean`), the official theorem name proved from it (`<entry>Spec.lean`), and a control with a weaker modulus (`<entry>NegWeak.lean`). The challenge is the official file of `epoch-research/LeanOpenProblems` (`apn/data/oeis/Isolated/`), copied byte for byte (`comparator-workspace/challenges/`).

## Checks and results

| Check | A361711 | A364175 | A364178 | Output |
|---|---|---|---|---|
| Build in the benchmark environment, no `sorry`, no error | pass | pass | pass | `outputs/<entry>-gates.txt` |
| `#print axioms` of `<entry>_from_target` and of the primed theorem (exact names) | propext, Classical.choice, Quot.sound | same | same | same |
| Keyword scan of the proof module and every module it imports | 0 hits (6 modules) | 0 hits (11 modules) | 0 hits (11 modules) | same |
| lean4checker on each of those modules | exit 0 | exit 0 | exit 0 | same |
| Module of origin of every constant in the final statement | Lean core, standard Mathlib, the target (`A361711`) | Lean core, standard Mathlib, the target (`a`) | Lean core, standard Mathlib, the target (`a`) | `outputs/<entry>-origin-audit.txt` |
| Comparator against the official challenge, Lean kernel and nanoda | accepted | accepted | accepted | `outputs/<entry>-comparator-nanoda.txt` |
| Comparator control: true but weaker statement (exponent 3r − 1) | rejected: statements do not match | rejected | rejected | `outputs/<entry>-comparator-neg-weak.txt` |

Tool versions as for A352275 (`verification/lean-checks/A352275/README.md`): Comparator 19e111e, lean4export cacf989, landrun 811cfff, nanoda_lib f67473b.

## Data check (added 2026-10-16)

The three target definitions were compared with the OEIS b-files (`scripts/gateA_older.py`, output `outputs/gateA_older.out`): A361711, the target's definition in ℤ, 26 terms (n = 1..26); A364175 and A364178, the exact integer formula that the Lean proofs show equal to the target's `a` (`a_eq_B175`, `a_eq_B178`), 15 and 13 terms; 0 mismatches. The targets' Gamma-ratio definitions themselves (`round(…).toNat`) were also evaluated with mpmath at a precision of (digits of the value + 40) for n ≤ 40 and agree with the integer formulas: 0 mismatches. (A first run at a fixed 80 digits showed differences from n = 29 on; these came from too little precision for numbers with hundreds of digits, and disappear at adequate precision.)
