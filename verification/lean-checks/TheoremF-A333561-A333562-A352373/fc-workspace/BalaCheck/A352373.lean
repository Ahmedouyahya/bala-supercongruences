import BalaCheck.TFMain
import BalaCheck.TFInst
import FormalConjectures.OEIS.Auto.«352373_a1d5fa75»

/-!
# A352373 from Theorem F

The target's `a n = Σ_{k ≤ n/2} C(3n-2k-1, n-2k) C(n+k-1, k)` (n ≥ 1) is
`[x^n] ((1-x)^{-2} (1-x^2)^{-1})^n = [x^n] ((1+x)^{-1} (1-x)^{-3})^n`,
i.e. Theorem F with `(a, b, c) = (-1, -3, 1)` (`TF.A_neg_one_neg_three`, `TF.tower_int`).
-/

theorem A352373_from_target : type_of% @oeis_a352373_supercongruence := by
  intro p hp hp5 n hn k hk
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
  exact TF.tower_int hp hp5 (-1) (-3) 1 a
    (fun N hN => by
      rw [TF.A_neg_one_neg_three N hN]
      simp only [a, if_neg (show N ≠ 0 by omega)]) hn hk
