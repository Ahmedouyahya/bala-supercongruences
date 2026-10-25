import BalaProofs.BalaGeneral
import BalaProofs.TFInst
import BalaProofs.A352373Defs

/-!
# A check of the definition `BalaGeneral.aRS`

Bala names A352373 as the case `r = -1`, `s = -3` of his general sequence `a(r,s;n)`. Here the
general definition `BalaGeneral.aRS (-1) (-3)` is shown to agree, for `n ≥ 1`, with the benchmark's
own definition of A352373 (`a` in `BalaProofs.A352373Defs`, copied verbatim from the benchmark file).
-/

open Finset

theorem aRS_neg_one_neg_three_eq_A352373 (N : ℕ) (hN : 1 ≤ N) :
    BalaGeneral.aRS (-1) (-3) N = (a N : ℤ) := by
  have h := BalaGeneral.coeffPow_eq_A (-1) (-3) 1 N
  rw [one_mul, TF.A_neg_one_neg_three N hN] at h
  have ha : (a N : ℚ) = ((∑ k ∈ range (N / 2 + 1),
      (3 * N - 2 * k - 1).choose (N - 2 * k) * (N + k - 1).choose k : ℕ) : ℚ) := by
    simp only [a, if_neg (show N ≠ 0 by omega)]
  have h2 : ((BalaGeneral.aRS (-1) (-3) N : ℤ) : ℚ) = ((a N : ℤ) : ℚ) := by
    rw [Int.cast_natCast, ha]; exact h
  exact_mod_cast h2
