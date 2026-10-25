import BalaProofs.TFSetup

/-!
# Theorem F, steps 2–3 of PLAN-route-b.md: the Frobenius–exp identity and the expansion (1)

`(p:ℚ) • F = expand p F + (p:ℚ) • L` (p odd), hence `φ^{pM} = φ(x^p)^M · exp(pM·L)`, and
`A(pM) - A(M) = Σ_{w < cM} [x^{p(cM-w)}] exp(pM·L) · [x^w] φ^M`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- The exponential factor `E = exp(N·L)` (used with `N = pM`). -/
def E (p : ℕ) (a b : ℤ) (N : ℕ) : ℚ⟦X⟧ := expS ((N : ℚ) • L p a b)

theorem constantCoeff_E (p : ℕ) (a b : ℤ) (N : ℕ) : constantCoeff (E p a b N) = 1 :=
  constantCoeff_expS _

variable {p : ℕ} [hp : Fact p.Prime]

theorem frob_F (hp2 : p ≠ 2) (a b : ℤ) :
    (p : ℚ) • F a b = expand p hp.out.ne_zero (F a b) + (p : ℚ) • L p a b := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  ext j
  rw [map_add, coeff_smul, coeff_smul, coeff_expand, smul_eq_mul, smul_eq_mul]
  simp only [F, L, Lc, coeff_mk]
  by_cases hj : p ∣ j
  · obtain ⟨i, rfl⟩ := hj
    rw [if_pos (dvd_mul_right p i), if_pos (dvd_mul_right p i), mul_zero, add_zero,
      Nat.mul_div_cancel_left i hp.out.pos]
    unfold fc
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [if_neg (mul_ne_zero hp.out.ne_zero hi), if_neg hi]
      have hsign : (-1 : ℚ) ^ (p * i + 1) = (-1) ^ (i + 1) := by
        rw [pow_succ, pow_succ, pow_mul, hodd.neg_one_pow]
      have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast hi
      rw [hsign, Nat.cast_mul]
      field_simp
  · rw [if_neg hj, if_neg hj, zero_add]

theorem Phi_pM (hp2 : p ≠ 2) (a b : ℤ) (M : ℕ) :
    Phi a b (p * M) = expand p hp.out.ne_zero (Phi a b M) * E p a b (p * M) := by
  have h1 : ∀ G : ℚ⟦X⟧, ((p * M : ℕ) : ℚ) • G = (M : ℚ) • ((p : ℚ) • G) := by
    intro G
    rw [smul_smul, Nat.cast_mul, mul_comm]
  rw [show Phi a b (p * M) = expS (((p * M : ℕ) : ℚ) • F a b) from rfl, h1, frob_F hp2,
    smul_add, ← expand_smul, expS_add, ← expand_expS _ _ hp.out.ne_zero, ← h1]
  rfl

theorem A_sub (hp2 : p ≠ 2) (a b : ℤ) (c M : ℕ) :
    A a b c (p * M) - A a b c M
      = ∑ w ∈ range (c * M), coeff (c * M * p - p * w) (E p a b (p * M)) * coeff w (Phi a b M) := by
  have h1 : A a b c (p * M)
      = coeff (c * M * p) (E p a b (p * M) * expand p hp.out.ne_zero (Phi a b M)) := by
    rw [A, Phi_pM hp2, mul_comm (expand _ _ _), show c * (p * M) = c * M * p by ring]
  have h0 : c * M * p - p * (c * M) = 0 := by
    rw [Nat.mul_comm p]
    exact Nat.sub_self _
  rw [h1, coeff_mul_expand, sum_range_succ, h0, coeff_zero_eq_constantCoeff, constantCoeff_E,
    one_mul]
  rw [show A a b c M = coeff (c * M) (Phi a b M) from rfl]
  ring

end

end TF
