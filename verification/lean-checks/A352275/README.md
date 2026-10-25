# Machine check of A352275 (every u_m)

Result: Bala's conjecture on A352275, in the form of the benchmark target `u_m_supercongruence_conjecture` (all m, n, r ≥ 1, all primes p ≥ 5), is proved in Lean and accepted by every check below. Checked on 2026-10-16.

## The proof in one paragraph

For n ≥ 1 each term n/(n+2k)·C(n+2k,k) of u_m(n) is the non-negative integer C(n+2k−1,k) − C(n+2k−1,k−1), which is `formalCatalanCoeff n k` in Epoch's accepted Lean proof of A333096; so the target's `Rat.floor` and `Int.toNat` change nothing, u_m(n) = `formalPartial n (m n)` = `FNat ((2m+1) n) (m n)` (Epoch's `formalPartial_eq_FNat`), and Epoch's `FNat_scale_supercongruence` with B = m·n·p^(r−1), Y = (m+1)·n·p^(r−1) gives the congruence modulo p^(3r). The hypothesis m > 0 is not used. Lemma map:

| Lean lemma (`BalaA352275.*`) | Statement | Paper step (`proofs/A352275-u_m-family.md`) |
|---|---|---|
| `choose_id1`, `choose_id2` | C(n+2k−1,k)(n+2k) = C(n+2k,k)(n+k); C(n+2k−1,k−1)(n+2k) = C(n+2k,k)·k | coefficient formula for c(x)^n |
| `fcc_nat` | `formalCatalanCoeff n k` = C(n+2k−1,k) − C(n+2k−1,k−1) for n, k ≥ 1 | same |
| `term_eq`, `term_toNat` | the target's ℚ term equals that integer, which is ≥ 0, so floor and `toNat` are exact | integrality of the terms |
| `u_eq_formalPartial`, `u_eq_FNat` | u_m(n) = FNat((2m+1)n, mn) | u_m(n) = FNat((2m+1)n, mn) |
| `u_scale` | the congruence modulo p^(3r) | application of `FNat_scale_supercongruence` |

## Where the files are

- Repository version (Lean v4.35.0, Mathlib as pinned in `lean/lake-manifest.json`): `lean/BalaProofs/A352275.lean`, importing `lean/BalaProofs/EpochA333096.lean`. The definitions `a`, `u`, the target's own `a_zero`…`a_three` and the statement of `u_m_supercongruence_conjecture` are verbatim from `statements/lean-targets/352275_4b1f2230.lean`; only the import lines differ.
- Benchmark-environment version (Lean v4.27.0, Formal Conjectures `auto_oeis` commit 67338a157bbb8d87e9a349d662f82a868bda6327): `fc-workspace/BalaCheck/A352275.lean`. It imports the unmodified target module `FormalConjectures.OEIS.Auto.«352275_4b1f2230»` and Epoch's file (`EpochSol`, made from `Submission/Spec.lean` of run `oeis-lite-200usd-sol-nk5wh4g0vh3546nm` in `epoch-research/LeanOpenProblems-results`, commit fd09021e, with one change: line 45 `def a` renamed `def a_unused_epoch`, because the target also defines `a`). Its final theorem is stated as `type_of% @u_m_supercongruence_conjecture`, so its statement is taken by Lean from the target file itself.
- Official checker setup: `comparator-workspace/` (the `Submission` modules and configurations; the challenge is `apn/data/oeis/Isolated/u_m_supercongruence_conjecture.lean` of `epoch-research/LeanOpenProblems`, used byte-identical, and `Submission/EpochOrig.lean` is Epoch's `Spec.lean` byte-identical).
- Outputs: `outputs/`. Scripts: `scripts/`.

## Checks and results

| Check | What it rules out | Result | Output |
|---|---|---|---|
| Definition mirrored in Python, compared with OEIS b-files of u_1 (A333093), u_2 (A352275), u_3 (A352276) | a target definition that is not Bala's sequence | 900 terms, 0 mismatches | `outputs/gateAB.out` |
| Every step of the bridge tested numerically | a false lemma | 13,331 cases, 0 failures; minimal slack 0 | `outputs/gateAB.out` |
| Build in the benchmark environment, scan for `sorry` and errors | unfinished proof | first run rejected (one argument name), fixed; second run clean | `outputs/gates-real-1.txt`, `outputs/gates-real-2.txt` |
| `#print axioms`, from a separate audit file, exact name match | hidden assumptions | `propext`, `Classical.choice`, `Quot.sound` only, for the final theorem, `u_scale`, `a = u 2` and the target's `a_one`…`a_three` | `outputs/gates-real-2.txt` |
| Keyword scan for tampering (30 keywords) over every new module | redefined notation, elaborators, environment edits | 15 hits, all `private` declarations in Epoch's file, reviewed in `fc-workspace/BalaCheck/GREP-ALLOW.txt` | `outputs/gates-real-2.txt` |
| lean4checker (v4.27.0) replay | tampered compiled files | exit 0 on both modules | `outputs/gates-real-2.txt` |
| Statement printed with `pp.explicit`; module of origin of every constant | a statement that differs from the target | constants only from Lean core, standard Mathlib definitions and the target module (`u`) | `outputs/origin-audit.txt` |
| Negative controls through the same gates: `sorry`, an added axiom, `native_decide`, `#exit` | gates that accept anything | all four rejected | `outputs/negative-controls.txt` |
| Comparator (leanprover, commit 19e111e; lean4export cacf989; landrun 811cfff, as pinned in the benchmark's Dockerfile) against the official challenge file | statement mismatch, extra axioms, kernel errors | accepted: "Your solution is okay!" | `outputs/comparator-run-1.txt` |
| Comparator controls: a proof by `sorry`; a true but weaker statement (modulus p^(3r−1)) | a checker that does not compare statements | rejected: "Illegal axiom detected: 'sorryAx'"; "Challenge and solution theorem statement do not match" | `outputs/comparator-neg-*.txt` |
| Comparator with the independent kernel nanoda (nanoda_lib f67473b) | an error in Lean's own kernel | both kernels accept | `outputs/comparator-nanoda.txt` |
| nanoda control: export with the proof of `choose_id1` placed on `choose_id2` | an external kernel that does not check | rejected by nanoda's type checker (`self.def_eq(u, v)` assertion); the genuine export: 17,461 declarations, no type-checker errors | `outputs/nanoda-direct-*.txt` |
| Repository version: build with Lean v4.35.0, axioms, `leanchecker` | a proof that only works in the benchmark environment | exit 0, no `sorry`; standard axioms for all seven theorems; `leanchecker` exit 0 on both modules | `outputs/repo-v4.35-*.txt` |

## What these checks do not cover

The kernel accepts any declared axiom, so the axiom audit and Comparator's axiom check, not the kernel replays, are what exclude `sorry` and added axioms. The checks show that the Lean theorem holds; that the Lean statement is Bala's conjecture rests on the reading of the definitions (above, and the Python comparison with the OEIS b-files).

## How to re-run

Benchmark environment: export Formal Conjectures at the commit above into a directory, add the library `BalaCheck` (globs `BalaCheck.+`) to its `lakefile.toml`, copy `fc-workspace/BalaCheck` and Epoch's file as described above, then `python3 -I scripts/gates.py <workspace> BalaCheck.A352275 BalaCheck/AuditA352275.lean A352275_from_target,BalaA352275.u_scale,A352275_a_eq_u2,a_one,a_two,a_three` (the script expects lean4checker built for v4.27.0; its path is set in the script). Official checker: the same export with the `Challenge` and `Submission` libraries appended as in the benchmark Dockerfile, the challenge file and Epoch's file copied as described, the files of `comparator-workspace/`, and `scripts/run-comparator.sh run/config.json <output>`. Repository version: `cd lean && lake env lean BalaProofs/A352275.lean`.
