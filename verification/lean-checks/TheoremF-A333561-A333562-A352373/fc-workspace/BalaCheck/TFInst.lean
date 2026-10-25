import BalaCheck.TFSetup

/-!
# Theorem F, step 9 of PLAN-route-b.md: coefficient formulas for A333561, A333562, A352373

* `(a,b,c) = (m,-1,c)`: `A(N) = Σ_{k ≤ cN} C(mN, cN-k) C(N+k-1, k)` (A333561: m = 3, c = 2;
  A333562 representation: m = 4, c = 3);
* `(a,b,c) = (-1,-3,1)`: `A(N) = Σ_{k ≤ N/2} C(3N-2k-1, N-2k) C(N+k-1, k)` (A352373).
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

theorem coeff_one_add_X_pow (m k : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ m) = ((m.choose k : ℕ) : ℚ) := by
  have h : (1 + X : ℚ⟦X⟧) ^ m
      = ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem Phi_m_neg_one (m N : ℕ) : Phi (m : ℤ) (-1) N = (1 + X) ^ (N * m) * c1S ^ N := by
  rw [Phi_eq_expS]
  have e1 : (((N : ℤ) * (m : ℤ) : ℤ) : ℚ) = ((N * m : ℕ) : ℚ) := by push_cast; ring
  have e2 : (((N : ℤ) * (-1) : ℤ) : ℚ) • lm = (N : ℚ) • (-lm) := by
    rw [smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  rw [e1, e2, Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_nsmul,
    expS_lp, expS_neg_lm]

theorem A_m_neg_one (m c N : ℕ) (hN : 1 ≤ N) :
    A (m : ℤ) (-1) c N = ((∑ k ∈ range (c * N + 1),
      Nat.choose (m * N) (c * N - k) * Nat.choose (N + k - 1) k : ℕ) : ℚ) := by
  rw [A, Phi_m_neg_one, mul_comm ((1 + X) ^ (N * m)), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  apply sum_congr rfl
  intro k _
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [coeff_c1S_pow, coeff_one_add_X_pow, mul_comm (N' + 1) m,
    show N' + 1 + k - 1 = N' + k by omega]
  ring

theorem sum_even (g : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (if 2 ∣ i then g i else 0) = ∑ k ∈ range (n / 2 + 1), g (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      have h2 : ¬ 2 ∣ n + 1 := by omega
      rw [h1, if_neg h2, add_zero]
    · have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [h1, sum_range_succ _ (n / 2 + 1), if_pos (by omega)]
      congr 2
      omega

theorem Phi_neg_one_neg_three (N : ℕ) :
    Phi (-1) (-3) N = expand 2 two_ne_zero (c1S ^ N) * c1S ^ (2 * N) := by
  rw [Phi_eq_expS]
  have e1 : (((N : ℤ) * (-1) : ℤ) : ℚ) • lp = (N : ℚ) • (-lp) := by
    rw [smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  have e2 : (((N : ℤ) * (-3) : ℤ) : ℚ) • lm = ((3 * N : ℕ) : ℚ) • (-lm) := by
    rw [smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  rw [e1, e2, Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_nsmul,
    expS_neg_lp, expS_neg_lm, map_pow]
  have h := one_sub_X_mul_c1S
  generalize (1 - X : ℚ⟦X⟧) = Y at h ⊢
  calc (expand 2 two_ne_zero c1S * Y) ^ N * c1S ^ (3 * N)
      = (expand 2 two_ne_zero c1S) ^ N * (Y * c1S) ^ N * c1S ^ (2 * N) := by ring
  _ = (expand 2 two_ne_zero c1S) ^ N * c1S ^ (2 * N) := by rw [h, one_pow, mul_one]

theorem A_neg_one_neg_three (N : ℕ) (hN : 1 ≤ N) :
    A (-1) (-3) 1 N = ((∑ k ∈ range (N / 2 + 1),
      (3 * N - 2 * k - 1).choose (N - 2 * k) * (N + k - 1).choose k : ℕ) : ℚ) := by
  rw [A, Phi_neg_one_neg_three, one_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_expand, ite_mul, zero_mul, Nat.succ_eq_add_one]
  rw [sum_even (fun i => coeff (i / 2) (c1S ^ N) * coeff (N - i) (c1S ^ (2 * N))) N]
  push_cast
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Nat.mul_div_cancel_left k two_pos, coeff_c1S_pow,
    show 2 * (N' + 1) = (2 * N' + 1) + 1 by ring, coeff_c1S_pow,
    show 2 * N' + 1 + (N' + 1 - 2 * k) = 3 * (N' + 1) - 2 * k - 1 by omega,
    show N' + 1 + k - 1 = N' + k by omega]
  ring

end

end TF
