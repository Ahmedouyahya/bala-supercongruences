import Submission.TFMain
import Submission.TFInst
import Submission.A333561Defs

/-!
# A333561 from Theorem F

The target's `a n = Σ_{k ≤ 2n} C(3n, 2n-k) C(n+k-1, k)` is `[x^{2n}] ((1+x)^3 (1-x)^{-1})^n`,
i.e. Theorem F with `(a, b, c) = (3, -1, 2)` (`TF.A_m_neg_one`, `TF.tower_int`).
-/

theorem A333561_full :
    ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((3 : ℕ) : ℤ) (-1) 2 a
    (fun N hN => by rw [TF.A_m_neg_one 3 2 N hN]; rfl) hn hk
  exact_mod_cast h
