import BalaCheck.TFMain
import BalaCheck.TFInst
import FormalConjectures.OEIS.Auto.«333561_b286c526»

/-!
# A333561 from Theorem F

The target's `a n = Σ_{k ≤ 2n} C(3n, 2n-k) C(n+k-1, k)` is `[x^{2n}] ((1+x)^3 (1-x)^{-1})^n`,
i.e. Theorem F with `(a, b, c) = (3, -1, 2)` (`TF.A_m_neg_one`, `TF.tower_int`).
-/

theorem A333561_from_target : type_of% @oeis_333561_conjecture := by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((3 : ℕ) : ℤ) (-1) 2 a
    (fun N hN => by rw [TF.A_m_neg_one 3 2 N hN]; rfl) hn hk
  exact_mod_cast h
