import Submission.TFHarmonic

/-!
# Theorem F, step 6 of PLAN-route-b.md: the ε-bound

For `p ∣ T`, `T ≠ 0`, `p^r ∣ N`, `r ≥ 1`, `p ≥ 5`:
`v_p([x^T] exp(N L)) ≥ min(2r + v_p T, 3r)`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

theorem coeff_L (p : ℕ) (a b : ℤ) (j : ℕ) : coeff j (L p a b) = Lc p a b j := coeff_mk _ _

theorem coeff_L_dvd {p : ℕ} (a b : ℤ) {j : ℕ} (hj : p ∣ j) : coeff j (L p a b) = 0 := by
  rw [coeff_L, Lc, if_pos hj]

theorem constantCoeff_L (p : ℕ) (a b : ℤ) : constantCoeff (L p a b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_L_dvd a b (dvd_zero p)]

variable {p : ℕ} [hp : Fact p.Prime]

theorem pint_L (a b : ℤ) : PInt p (L p a b) := by
  intro j
  rw [coeff_L, Lc]
  split_ifs with hj
  · exact V_zero_val _
  · unfold fc
    have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero p)
    rw [if_neg hj0, div_eq_mul_one_div]
    have h := V_mul (V_intcast (p := p) (a * (-1) ^ (j + 1) - b)
      (q := (a : ℚ) * (-1) ^ (j + 1) - b) (by push_cast; ring))
      (V_inv_unit hj0 hj)
    rwa [add_zero] at h

theorem eps_bound (hp5 : 5 ≤ p) (a b : ℤ) {N r : ℕ} (hN : p ^ r ∣ N) (hr : 1 ≤ r)
    {T : ℕ} (hT0 : T ≠ 0) (hpT : p ∣ T) {k : ℤ}
    (hk1 : k ≤ 2 * (r : ℤ) + padicValNat p T) (hk2 : k ≤ 3 * (r : ℤ)) :
    V p k (coeff T (expS ((N : ℚ) • L p a b))) := by
  have hc0 : constantCoeff ((N : ℚ) • L p a b) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_L_dvd a b (dvd_zero p),
      smul_zero]
  have hNV : V p r (N : ℚ) := (V_nat_iff_dvd r N).mpr hN
  rw [coeff_expS _ hc0]
  apply V_sum
  intro ℓ _
  rw [smul_pow, coeff_smul, smul_eq_mul]
  have hfac : V p (-(padicValNat p ℓ.factorial : ℤ)) ((ℓ.factorial : ℚ))⁻¹ := by
    have := V_inv_nat (p := p) (n := ℓ.factorial) ℓ.factorial_ne_zero
    rwa [one_div] at this
  rcases Nat.lt_or_ge ℓ 2 with hl | hl
  · interval_cases ℓ
    · simp [coeff_one, hT0]
    · simp [coeff_L_dvd a b hpT]
  · have hv := factorial_val_bound (p := p) hp5 (show 1 ≤ ℓ by omega)
    rcases Nat.lt_or_ge ℓ 3 with hl3 | hl3
    · obtain rfl : ℓ = 2 := by omega
      have h := V_mul hfac (V_mul (V_pow hNV 2) (V_coeff_L_sq hp5 a b hT0 hpT))
      apply V_mono h
      have h0 : padicValNat p (Nat.factorial 2) = 0 := by omega
      rw [h0]
      omega
    · have h := V_mul hfac (V_mul (V_pow hNV ℓ) (V_coeff_pow (pint_L (p := p) a b) ℓ T))
      apply V_mono h
      have hvl : (padicValNat p ℓ.factorial : ℤ) ≤ (ℓ : ℤ) - 3 := by omega
      have h3 : (ℓ : ℤ) - 3 ≤ (ℓ : ℤ) * r - 3 * r := by
        have hl' : (0 : ℤ) ≤ (ℓ : ℤ) - 3 := by omega
        have hr' : (0 : ℤ) ≤ (r : ℤ) - 1 := by omega
        nlinarith [mul_nonneg hl' hr']
      have h4 : (ℓ : ℤ) * 0 = 0 := by ring
      linarith

end

end TF
