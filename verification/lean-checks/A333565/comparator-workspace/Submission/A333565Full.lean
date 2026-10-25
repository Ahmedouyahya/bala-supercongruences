import Submission.A333565Bridge
import Submission.TFMain
import Submission.TFInst
import Submission.TF3Main

/-!
# A333565 from Theorem F (p ≥ 5) and Theorem F₃(ii) (p = 3)

`A333565 n = 2 B(n) - (-1)^n` (`A333565.A333565_eq`), and `B(N) = [x^N] ((1+x)^2 (1-x)^{-1})^N`
for `N ≥ 1` (`A333565.B_eq_coeffForm`, `TF.A_m_neg_one 2 1`), i.e. `(a, b, c) = (2, -1, 1)`.
For `p ≥ 5` use `TF.tower_int`, for `p = 3` use `TF.tower_three`; since `p` is odd, `n p^k` and
`n p^{k-1}` have the same parity, so `A333565(n p^k) - A333565(n p^{k-1}) = 2 (B(n p^k) - B(n p^{k-1}))`.
-/

theorem A333565_full :
    ∀ (p n k : ℕ), Nat.Prime p → 3 ≤ p → n > 0 → k > 0 →
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] := by
  intro p n k hp hp3 hn hk
  have hB : ∀ N, 1 ≤ N → ((A333565.B N : ℕ) : ℚ) = TF.A 2 (-1) 1 N := by
    intro N hN
    have h := TF.A_m_neg_one 2 1 N hN
    rw [Nat.cast_ofNat] at h
    rw [h, A333565.B_eq_coeffForm N hN]
    simp only [one_mul]
  have hdiv : (p : ℤ) ^ (3 * k)
      ∣ (A333565.B (n * p ^ k) : ℤ) - (A333565.B (n * p ^ (k - 1)) : ℤ) := by
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · obtain rfl : p = 3 := by
        interval_cases p
        · rfl
        · exact absurd hp (by norm_num)
      exact_mod_cast TF.tower_three A333565.B hB hn hk
    · exact TF.tower_int hp h5 2 (-1) 1 A333565.B hB hn hk
  have hodd : ¬ Even p := by
    rw [hp.even_iff]
    omega
  have hpar : Even (n * p ^ k) ↔ Even (n * p ^ (k - 1)) := by
    simp [Nat.even_mul, Nat.even_pow, hodd]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd, A333565.A333565_diff _ _ hpar]
  exact Dvd.dvd.mul_left hdiv 2
