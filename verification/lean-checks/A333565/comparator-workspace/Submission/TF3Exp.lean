import Submission.TFFrob
import Submission.TFEps
import Submission.TFLift

/-!
# Theorem F at p = 3 (PLAN items 5–6): the expansion of `[x^{3t}] exp(N L)` and the cubic term

For `N = 3M`, `r = 1 + v_3 M`, `t ≥ 1`:
`[x^{3t}] exp(N L) ≡ (N²/2) [x^{3t}] L² + (N³/6) [x^{3t}] L³ (mod 3^{3r})` (Lemmas B, C), and
`[x^{3t}] L³ ≡ [x^t] L (mod 3)` (Lemma D, Frobenius `frob_full`).
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- `2 v_3(ℓ!) ≤ ℓ - 1` for `ℓ ≥ 1` (Legendre at p = 3). -/
theorem two_mul_val_factorial_le {ℓ : ℕ} (hl : ℓ ≠ 0) : 2 * padicValNat 3 ℓ.factorial < ℓ := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 hl
  simpa using h

/-- Lemmas B and C at p = 3. -/
theorem coeff_E_three (a b : ℤ) {M t : ℕ} (ht : t ≠ 0) :
    V 3 (3 * (1 + (padicValNat 3 M : ℤ)))
      (coeff (3 * t) (E 3 a b (3 * M))
        - ((3 * M : ℕ) : ℚ) ^ 2 / 2 * coeff (3 * t) (L 3 a b ^ 2)
        - ((3 * M : ℕ) : ℚ) ^ 3 / 6 * coeff (3 * t) (L 3 a b ^ 3)) := by
  set N := 3 * M with hN
  set r := 1 + padicValNat 3 M with hr
  have hNr : 3 ^ r ∣ N := by
    rw [hr, pow_add, pow_one, hN]
    exact mul_dvd_mul_left 3 pow_padicValNat_dvd
  have hNV : V 3 (r : ℤ) (N : ℚ) := (V_nat_iff_dvd r N).mpr hNr
  have hc0 : constantCoeff ((N : ℚ) • L 3 a b) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_L_dvd a b (dvd_zero 3), smul_zero]
  set f : ℕ → ℚ := fun ℓ => ((ℓ.factorial : ℚ))⁻¹ * ((N : ℚ) ^ ℓ * coeff (3 * t) (L 3 a b ^ ℓ))
    with hf
  have hexp : coeff (3 * t) (E 3 a b N) = ∑ ℓ ∈ range (3 * t + 1), f ℓ := by
    rw [E, coeff_expS _ hc0]
    apply sum_congr rfl
    intro ℓ _
    rw [hf, smul_pow, coeff_smul, smul_eq_mul]
  have hT0 : 3 * t ≠ 0 := by omega
  have h0 : f 0 = 0 := by
    rw [hf]
    simp only [pow_zero, coeff_one, if_neg hT0, mul_zero]
  have h1 : f 1 = 0 := by
    rw [hf]
    simp only [pow_one, coeff_L_dvd a b (dvd_mul_right 3 t), mul_zero]
  have h2 : f 2 = (N : ℚ) ^ 2 / 2 * coeff (3 * t) (L 3 a b ^ 2) := by
    rw [hf]
    simp only [Nat.factorial_two]
    push_cast
    ring
  have h3 : f 3 = (N : ℚ) ^ 3 / 6 * coeff (3 * t) (L 3 a b ^ 3) := by
    rw [hf]
    simp only [show Nat.factorial 3 = 6 by rfl]
    push_cast
    ring
  obtain ⟨u, hu⟩ : ∃ u, 3 * t + 1 = 4 + u := ⟨3 * t - 3, by omega⟩
  have hsplit : ∑ ℓ ∈ range (3 * t + 1), f ℓ
      = f 0 + f 1 + f 2 + f 3 + ∑ x ∈ range u, f (4 + x) := by
    rw [hu, sum_range_add]
    simp only [sum_range_succ, range_zero, sum_empty, zero_add]
  rw [hexp, hsplit, h0, h1, h2, h3]
  have heq : (0 : ℚ) + 0 + (N : ℚ) ^ 2 / 2 * coeff (3 * t) (L 3 a b ^ 2)
      + (N : ℚ) ^ 3 / 6 * coeff (3 * t) (L 3 a b ^ 3) + ∑ x ∈ range u, f (4 + x)
      - (N : ℚ) ^ 2 / 2 * coeff (3 * t) (L 3 a b ^ 2)
      - (N : ℚ) ^ 3 / 6 * coeff (3 * t) (L 3 a b ^ 3) = ∑ x ∈ range u, f (4 + x) := by ring
  rw [heq]
  apply V_sum
  intro x _
  set ℓ := 4 + x with hℓ
  have hfac : V 3 (-(padicValNat 3 ℓ.factorial : ℤ)) ((ℓ.factorial : ℚ))⁻¹ := by
    have := V_inv_nat (p := 3) (n := ℓ.factorial) ℓ.factorial_ne_zero
    rwa [one_div] at this
  have hco := V_coeff_pow (pint_L (p := 3) a b) ℓ (3 * t)
  have h := V_mul hfac (V_mul (V_pow hNV ℓ) hco)
  apply V_mono h
  have hv := two_mul_val_factorial_le (show ℓ ≠ 0 by omega)
  have hv' : padicValNat 3 ℓ.factorial + 3 ≤ ℓ := by omega
  have hv'' : (padicValNat 3 ℓ.factorial : ℤ) + 3 ≤ (ℓ : ℤ) := by exact_mod_cast hv'
  have hr1 : (1 : ℤ) ≤ (r : ℤ) := by omega
  have hl4 : (4 : ℤ) ≤ (ℓ : ℤ) := by omega
  have hprod : (0 : ℤ) ≤ ((ℓ : ℤ) - 3) * ((r : ℤ) - 1) :=
    mul_nonneg (by omega) (by omega)
  have hrr : ((1 + padicValNat 3 M : ℕ) : ℤ) = (r : ℤ) := by rw [hr]
  push_cast at hrr ⊢
  nlinarith

/-- Lemma D: `[x^{3t}] L³ ≡ [x^t] L (mod 3)`. -/
theorem cubic_three (a b : ℤ) (t : ℕ) :
    V 3 1 (coeff (3 * t) (L 3 a b ^ 3) - coeff t (L 3 a b)) := by
  have h := frob_full (p := 3) (pint_L (p := 3) a b) (3 * t)
  rwa [map_sub, coeff_expand_mul] at h

end

end TF
