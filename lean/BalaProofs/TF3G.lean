import BalaProofs.TF3Harm
import BalaProofs.TFEps

/-!
# Theorem F at p = 3 (PLAN items 7 and 9): the series `g` (Lemma H) for `(a, b) = (2, -1)`

`gc t = [x^{3t}] L² / t` (`t ≥ 1`), `gc 0 = 0`. By `coeff_L_sq` (Lemma G) and `H_three`, `Hpm_three`:
`gc t` is 3-integral and `gc t ≡ a²(-1)^t + b² = 4(-1)^t + 1 (mod 3)`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- `g_t = [x^{3t}] L² / t` for `t ≥ 1`, `g_0 = 0` (p = 3, (a, b) = (2, -1)). -/
def gc (t : ℕ) : ℚ := if t = 0 then 0 else coeff (3 * t) (L 3 2 (-1) ^ 2) / (t : ℚ)

/-- the series `g = Σ g_t y^t`. -/
def gS : ℚ⟦X⟧ := mk gc

theorem gc_mul {t : ℕ} (ht : t ≠ 0) : (t : ℚ) * gc t = coeff (3 * t) (L 3 2 (-1) ^ 2) := by
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  unfold gc
  rw [if_neg ht]
  field_simp

/-- Lemma H(b) for `(a, b) = (2, -1)`: `g_t ≡ 4 (-1)^t + 1 (mod 3)` for `t ≥ 1`. -/
theorem gc_cong {t : ℕ} (ht : t ≠ 0) : V 3 1 (gc t - (4 * (-1) ^ t + 1)) := by
  have hT0 : 3 * t ≠ 0 := by omega
  have h3T : 3 ∣ 3 * t := dvd_mul_right 3 t
  have hw : padicValNat 3 (3 * t) = 1 + padicValNat 3 t := by
    rw [padicValNat.mul (by norm_num) ht, padicValNat.self (by norm_num)]
  have hsq := coeff_L_sq (p := 3) 2 (-1) h3T
  have hsign : (-1 : ℚ) ^ (3 * t) = (-1) ^ t := by rw [pow_mul]; norm_num
  have hgc := gc_mul ht
  have hH := H_three hT0 h3T
  rw [hw] at hH
  have hkey : ((3 * t ^ 2 : ℕ) : ℚ) * (gc t - (4 * (-1) ^ t + 1))
      = (4 * (-1) ^ t + 1) * (2 * ∑ i ∈ range (3 * t), hh 3 i - ((3 * t : ℕ) : ℚ) ^ 2 / 3)
        + 4 * (1 + (-1) ^ t) * ∑ i ∈ range (3 * t), (-1 : ℚ) ^ (i + 1) * hh 3 i := by
    rw [hsign] at hsq
    have h2 : (3 * (t : ℚ) ^ 2) * gc t = 3 * t * coeff (3 * t) (L 3 2 (-1) ^ 2) := by
      rw [← hgc]; ring
    push_cast at hsq ⊢
    linear_combination h2 + hsq
  have hc : V 3 0 ((4 : ℚ) * (-1) ^ t + 1) := V_intcast (4 * (-1) ^ t + 1) (by push_cast; ring)
  have hV : V 3 (2 * (1 + (padicValNat 3 t : ℤ)))
      (((3 * t ^ 2 : ℕ) : ℚ) * (gc t - (4 * (-1) ^ t + 1))) := by
    rw [hkey]
    apply V_add
    · have h := V_mul hc hH
      rw [zero_add] at h
      exact_mod_cast h
    · rcases Nat.even_or_odd t with hev | hodd
      · have hpm := Hpm_three hT0 h3T (by obtain ⟨m, hm⟩ := hev; exact ⟨3 * m, by omega⟩)
        rw [hw] at hpm
        have hc2 : V 3 0 ((4 : ℚ) * (1 + (-1) ^ t)) := V_intcast 8 (by rw [hev.neg_one_pow]; norm_num)
        have h := V_mul hc2 hpm
        rw [zero_add] at h
        exact_mod_cast h
      · rw [hodd.neg_one_pow]
        simp
  have hn0 : 3 * t ^ 2 ≠ 0 := by positivity
  have hv : padicValNat 3 (3 * t ^ 2) = 1 + 2 * padicValNat 3 t := by
    rw [padicValNat.mul (by norm_num) (pow_ne_zero 2 ht), padicValNat.self (by norm_num),
      padicValNat.pow t 2]
  have hdiv := V_div_nat hV hn0
  have hnQ : ((3 * t ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hn0
  rw [mul_div_cancel_left₀ _ hnQ, hv] at hdiv
  apply V_mono hdiv
  push_cast
  omega

end

end TF
