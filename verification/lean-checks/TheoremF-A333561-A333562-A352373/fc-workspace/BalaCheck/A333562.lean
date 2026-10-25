import BalaCheck.TFMain
import BalaCheck.TFInst
import BalaCheck.A333562Ident

/-!
# A333562 from Theorem F

By `A333562.a_eq_rep`, the target's `a n = Σ_{j ≤ 3n} C(n+j-1, j) 2^j` equals
`Σ_{k ≤ 3n} C(4n, 3n-k) C(n+k-1, k) = [x^{3n}] ((1+x)^4 (1-x)^{-1})^n` for `n ≥ 1`,
i.e. Theorem F with `(a, b, c) = (4, -1, 3)` (`TF.A_m_neg_one`, `TF.tower_int`).
-/

theorem A333562_from_target : type_of% @oeis_333562_conjecture_0_congruence := by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((4 : ℕ) : ℤ) (-1) 3 a
    (fun N hN => by rw [TF.A_m_neg_one 4 3 N hN, A333562.a_eq_rep N hN]) hn hk
  exact_mod_cast h
