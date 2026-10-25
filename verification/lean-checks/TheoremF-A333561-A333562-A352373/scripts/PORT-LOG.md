# Repository port of Theorem F and A333561, A333562, A352373 (Lean v4.27.0 -> v4.35.0), 2026-10-16

Source (not modified): `lean-check/fc-ws/BalaCheck/` (Lean v4.27.0, Mathlib v4.27.0).
Destination: `lean/BalaProofs/BalaProofs/` (Lean v4.35.0, Mathlib master as already fetched; no `lake update`).
Only new files were written there: EpochA333042, TFSetup, TFFrob, TFHarmonic, TFEps, TFLift, TFMain, TFInst,
A333562Ident, and A333561Defs/Main/(final), A333562Defs/Main/(final), A352373Defs/Main/(final).

## Reproduce
1. `python make_repo.py` — mechanical generation (see its docstring): import renames, Epoch header + `import Mathlib`,
   Defs/statement blocks copied verbatim from the frozen targets, Main = instance file without the `type_of%` theorem.
   Generator-level adaptations (not edits of proofs):
   - `import BalaCheck.EpochExp` -> `import BalaProofs.EpochA333042` (the file is named EpochA333042 in the repository;
     namespace `Epoch333042` is unchanged, so the TF files' `open ... Epoch333042.Super` needs no change).
   - A333562.lean: first line of the proof `intro p n k hp hp5 hn hk` -> `intro hp hp5 hn hk`, because the target
     statement binds `(p n k : ℕ)` before the colon. A333561 and A352373 keep their `intro` lines unchanged.
2. `python manual_fixes.py` — replays exactly the manual edits below (each with an occurrence-count assertion).
   Re-running steps 1+2 reproduces all 18 files byte for byte (checked with sha256sum).

## Manual edits (line numbers are those of the final repository file)
Source line for EpochA333042 = final line − 15 for final lines ≥ 76 (14 header lines added, 3 option lines removed).

| # | File | Line(s) | Old -> New | Reason |
|---|------|---------|------------|--------|
| 1 | EpochA333042.lean | 6–19 | (none) -> list of the changes below in the header comment | requested change list |
| 2 | EpochA333042.lean | src 58–60 (removed; would be after final line 75) | `set_option linter.style.copyright.formalConjectures false`, `set_option linter.style.moduleDocstring false`, `set_option linter.style.namespace false` -> deleted | These options are registered by Formal Conjectures' linters (`FormalConjectures/Util/Linters/{Copyright,ModuleDocstring,Namespace}Linter.lean`), not by Mathlib; with `import Mathlib` Lean v4.35 reports `Unknown option`. This is the only Formal Conjectures utility the file used. |
| 3 | EpochA333042.lean | 280, 286, 289, 300, 302, 442, 459, 462, 3550, 3560, 3728, 3729, 3738, 3739, 3740, 3750, 3770, 3771, 3774, 3775, 3776, 3783, 3784, 3801, 3906, 3907, 3914 (30 occurrences) | `d⁄dX ℚ` -> `d⁄dX` | v4.27 Mathlib: `variable (R)` … `def derivative : Derivation R R⟦X⟧ R⟦X⟧` (ring explicit, notation used as `d⁄dX ℚ`). Current Mathlib: `{R : Type*}`, `scoped notation "d⁄dX" => derivative` (ring implicit); `d⁄dX ℚ G` failed with "Application type mismatch". |
| 4 | EpochA333042.lean | 1559 (vc_add_eq) | `padicValNat.pow _ (Nat.factorial_ne_zero k)` -> `padicValNat.pow k.factorial m` | Signature changed from `pow (n : ℕ) (ha : a ≠ 0)` to `pow (a n : ℕ)` (no nonzero hypothesis). |
| 5 | EpochA333042.lean | 2371 (coeff_pow_congr), 2443 (coeff_trunc_pow_key) | `rw [Finset.mem_antidiagonal] at hx` -> `rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx` | Mathlib renamed `Finset.addAntidiagonal`/`mem_addAntidiagonal` to `Finset.antidiagonal`/`mem_antidiagonal` (deprecated aliases dated 2026-06-08 in `Mathlib/Data/Finset/MulAntidiagonal.lean`); these now take precedence over the `HasAntidiagonal` names exported to `Finset`, and the rewrite found no `Finset.antidiagonal ?s ?t ?a` pattern. Same fix as in EpochA333096.lean. |
| 6 | EpochA333042.lean | 3390, 3392 (coeff_mul_expand) | `Finset.antidiagonal (n*t)` -> `Finset.HasAntidiagonal.antidiagonal (n*t)` | same rename; error "Type mismatch … expected Set.IsPWO". |
| 7 | EpochA333042.lean | 3553 (d_c1S) | `Finset.antidiagonal k` -> `Finset.HasAntidiagonal.antidiagonal k` | same rename (was masked in the first compile by the `d⁄dX ℚ` error in the statement of d_c1S; fixed pre-emptively). |
| 8 | EpochA333042.lean | 298 (isExpOf_iff_deriv) | `simp only at this` -> `try simp only at this` | Lean v4.35: "`simp` made no progress" (the hypothesis from `have := congrArg (fun φ => coeff k φ) hD` is apparently already beta-reduced); following steps unchanged. Same device as `try dsimp` in EpochA333096.lean. |
| 9 | EpochA333042.lean | 457 (coeff_succ_pow_succ) | `simp only at h` -> `try simp only at h` | same as 8. |
| 10 | EpochA333042.lean | 4071 (gec_eq_coeff) | `simp only at hS ⊢` -> `try simp only at hS ⊢` | same error after `rw [gec_succ]`; following steps unchanged. |
| 11 | TFLift.lean | 31 | `rw [mem_antidiagonal] at hx` -> `rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx` | with `open Finset`, `mem_antidiagonal` is now ambiguous ("Ambiguous term": `HasAntidiagonal.mem_antidiagonal` vs the renamed `Finset.mem_antidiagonal`); same rename as 5. |

No other file needed a manual edit. No `set_option` was added; Epoch's six remaining options (`linter.unusedSectionVars`,
`linter.unnecessarySimpa`, `linter.unusedVariables`, `linter.unusedTactic`, `linter.dupNamespace`, `maxHeartbeats 2000000`)
are unchanged. Deprecation warnings (`if_pos`/`if_neg`, `push_neg`, …) compile and were left alone.

## Compile (each: `systemd-run --user --scope -q -p MemoryMax=6G nice -n 10 ~/.elan/bin/lake env lean -o … -i … BalaProofs/<M>.lean`)
Final exit codes, in dependency order (logs `repo-<M>.log`, 0 errors and no `sorry` in each):
EpochA333042 0, TFSetup 0, TFFrob 0, TFHarmonic 0, TFEps 0, TFLift 0, TFMain 0, TFInst 0, A333561Defs 0, A333562Defs 0,
A352373Defs 0, A333562Ident 0, A333561Main 0, A333562Main 0, A352373Main 0, A333561 0, A333562 0, A352373 0.
Earlier failing runs: EpochA333042 (1st: 48 errors -> edits 2–7, 10; 2nd: 2 errors -> edits 8–9; 3rd: exit 0), TFSetup
(1st: exit 1, missing `BalaProofs.EpochExp` -> generator import mapping), TFLift (1st: exit 1 -> edit 11).
EpochA333042 was compiled a final time after the header list (edit 1) was added (exit 0); the downstream modules were
compiled against the previous build of it, whose source differed only in that comment.

## Axioms (`repo-v4.35-axioms.txt`)
oeis_333561_conjecture, oeis_333562_conjecture_0_congruence, oeis_a352373_supercongruence, TF.theoremF:
each depends on [propext, Classical.choice, Quot.sound].
