import BalaProofs.TFSetup

/-!
# Theorem F, steps 4–5 of PLAN-route-b.md: harmonic sums over units and Lemma 4 (coefficients of `L²`)

`H_T = Σ_{0<i<T, p∤i} 1/i` is bounded by Epoch's `H_law` (Wolstenholme over units, p ≥ 5);
the alternating sum is `H_T^± = H_T - H_{T/2}` for even `T`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- `hh p i = 1/i` if `p ∤ i`, else `0` (so `hh p 0 = 0`). -/
def hh (p : ℕ) (i : ℕ) : ℚ := if p ∣ i then 0 else ((i : ℚ))⁻¹

variable {p : ℕ} [hp : Fact p.Prime]

/-- an integer-valued rational is `p`-integral. -/
theorem V_intcast (z : ℤ) {q : ℚ} (h : (z : ℚ) = q) : V p 0 q := h ▸ V_int z

theorem not_dvd_two (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)

theorem hh_two_mul (hp2 : p ≠ 2) (m : ℕ) : hh p m = 2 * hh p (2 * m) := by
  unfold hh
  by_cases hm : p ∣ m
  · rw [if_pos hm, if_pos (dvd_mul_of_dvd_right hm 2), mul_zero]
  · have h2m : ¬ p ∣ 2 * m := by
      intro h
      rcases (Nat.Prime.dvd_mul hp.out).mp h with h2 | h2
      · exact not_dvd_two hp2 h2
      · exact hm h2
    rw [if_neg hm, if_neg h2m, Nat.cast_mul, Nat.cast_two, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ two_ne_zero, one_mul]

theorem alt_sum (hp2 : p ≠ 2) (m : ℕ) :
    ∑ i ∈ range (2 * m), (-1 : ℚ) ^ (i + 1) * hh p i
      = ∑ i ∈ range (2 * m), hh p i - ∑ k ∈ range m, hh p k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [sum_range_succ]
    rw [ih, hh_two_mul hp2 m]
    have e1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e2 : (-1 : ℚ) ^ (2 * m + 1 + 1) = 1 := by rw [pow_succ, e1]; norm_num
    rw [e1, e2]
    ring

theorem H_bound (hp5 : 5 ≤ p) {N : ℕ} (hN : N ≠ 0) :
    V p (2 * (padicValNat p N : ℤ)) (∑ i ∈ range N, hh p i) := by
  have h := H_law (p := p) hp5 hN
  rw [sum_filter] at h
  have e : ∑ i ∈ range N, hh p i = ∑ k ∈ range N, if ¬ p ∣ k then ((k : ℚ))⁻¹ else 0 := by
    apply sum_congr rfl
    intro i _
    unfold hh
    rw [ite_not]
  rw [e]
  exact h

theorem Hpm_bound (hp5 : 5 ≤ p) {T : ℕ} (hT0 : T ≠ 0) (hT2 : 2 ∣ T) :
    V p (2 * (padicValNat p T : ℤ)) (∑ i ∈ range T, (-1 : ℚ) ^ (i + 1) * hh p i) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, rfl⟩ := hT2
  have hm : m ≠ 0 := by rintro rfl; simp at hT0
  have hv : padicValNat p (2 * m) = padicValNat p m := by
    rw [padicValNat.mul two_ne_zero hm, padicValNat.eq_zero_of_not_dvd (not_dvd_two hp2),
      zero_add]
  rw [alt_sum hp2 m]
  have h1 := H_bound hp5 hT0
  have h2 := H_bound hp5 hm
  rw [hv] at h1 ⊢
  exact V_sub h1 h2

omit hp in
theorem coeff_L_sq (a b : ℤ) {T : ℕ} (hpT : p ∣ T) :
    (T : ℚ) * coeff T (L p a b ^ 2)
      = 2 * ((((a : ℚ) ^ 2 * (-1) ^ T + (b : ℚ) ^ 2)) * ∑ i ∈ range T, hh p i
          - (a : ℚ) * b * (1 + (-1) ^ T) * ∑ i ∈ range T, (-1 : ℚ) ^ (i + 1) * hh p i) := by
  set nn : ℕ → ℚ := fun i =>
    ((a : ℚ) * (-1) ^ (i + 1) - b) * ((a : ℚ) * (-1) ^ (T - i + 1) - b) with hnn
  have hcoeff : coeff T (L p a b ^ 2) = ∑ i ∈ range (T + 1), Lc p a b i * Lc p a b (T - i) := by
    rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [L, coeff_mk]
  have hterm : ∀ i ∈ range (T + 1), (T : ℚ) * (Lc p a b i * Lc p a b (T - i))
      = hh p i * nn i + hh p (T - i) * nn (T - i) := by
    intro i hi
    rw [mem_range] at hi
    by_cases hpi : p ∣ i
    · have hpi' : p ∣ T - i := Nat.dvd_sub hpT hpi
      simp [Lc, hh, hpi, hpi']
    · have hpi' : ¬ p ∣ T - i := by
        intro h
        apply hpi
        have := Nat.dvd_sub hpT h
        rwa [Nat.sub_sub_self (by omega)] at this
      have hi0 : i ≠ 0 := by rintro rfl; exact hpi (dvd_zero p)
      have hTi0 : T - i ≠ 0 := by intro h; exact hpi' (h ▸ dvd_zero p)
      have hnn' : nn (T - i) = nn i := by
        simp only [hnn, Nat.sub_sub_self (by omega : i ≤ T)]
        ring
      rw [hnn']
      simp only [Lc, hh, fc, if_neg hpi, if_neg hpi', if_neg hi0, if_neg hTi0, hnn]
      have hcast : ((T - i : ℕ) : ℚ) = (T : ℚ) - i := by rw [Nat.cast_sub (by omega)]
      have hi0' : (i : ℚ) ≠ 0 := by exact_mod_cast hi0
      have hTi0' : (T : ℚ) - i ≠ 0 := by rw [← hcast]; exact_mod_cast hTi0
      rw [hcast]
      field_simp
      ring
  have hsum : (T : ℚ) * coeff T (L p a b ^ 2) = 2 * ∑ i ∈ range (T + 1), hh p i * nn i := by
    rw [hcoeff, mul_sum, sum_congr rfl hterm, sum_add_distrib]
    have hrefl : ∑ i ∈ range (T + 1), hh p (T - i) * nn (T - i)
        = ∑ i ∈ range (T + 1), hh p i * nn i := by
      have := sum_range_reflect (fun i => hh p i * nn i) (T + 1)
      rw [Nat.add_sub_cancel] at this
      exact this
    rw [hrefl]
    ring
  have hnn_eq : ∀ i ∈ range (T + 1), hh p i * nn i
      = ((a : ℚ) ^ 2 * (-1) ^ T + (b : ℚ) ^ 2) * hh p i
        - (a : ℚ) * b * (1 + (-1) ^ T) * ((-1 : ℚ) ^ (i + 1) * hh p i) := by
    intro i hi
    rw [mem_range] at hi
    have hsq : ((-1 : ℚ) ^ (i + 1)) ^ 2 = 1 := by
      rw [← pow_mul, pow_mul']
      norm_num
    have hs : (-1 : ℚ) ^ (T - i + 1) = (-1) ^ T * (-1) ^ (i + 1) := by
      have h1 : (-1 : ℚ) ^ (T - i + 1) * (-1) ^ (i + 1) = (-1) ^ T := by
        rw [← pow_add, show T - i + 1 + (i + 1) = T + 2 by omega, pow_add]
        norm_num
      calc (-1 : ℚ) ^ (T - i + 1) = (-1) ^ (T - i + 1) * ((-1) ^ (i + 1)) ^ 2 := by
            rw [hsq, mul_one]
      _ = ((-1) ^ (T - i + 1) * (-1) ^ (i + 1)) * (-1) ^ (i + 1) := by ring
      _ = (-1) ^ T * (-1) ^ (i + 1) := by rw [h1]
    simp only [hnn, hs]
    linear_combination (hh p i * (a : ℚ) ^ 2 * (-1) ^ T) * hsq
  have hT : hh p T = 0 := by
    unfold hh
    rw [if_pos hpT]
  rw [hsum, sum_congr rfl hnn_eq, sum_range_succ, hT, mul_zero, mul_zero, mul_zero, sub_zero,
    add_zero, sum_sub_distrib, ← mul_sum, ← mul_sum]

theorem V_coeff_L_sq (hp5 : 5 ≤ p) (a b : ℤ) {T : ℕ} (hT0 : T ≠ 0) (hpT : p ∣ T) :
    V p (padicValNat p T : ℤ) (coeff T (L p a b ^ 2)) := by
  have hT : (T : ℚ) ≠ 0 := by exact_mod_cast hT0
  have h := coeff_L_sq (p := p) a b hpT
  set X1 : ℚ := ((a : ℚ) ^ 2 * (-1) ^ T + (b : ℚ) ^ 2) * ∑ i ∈ range T, hh p i with hX1
  set X2 : ℚ := (a : ℚ) * b * (1 + (-1) ^ T) * ∑ i ∈ range T, (-1 : ℚ) ^ (i + 1) * hh p i
    with hX2
  have hc1 : V p 0 ((a : ℚ) ^ 2 * (-1) ^ T + (b : ℚ) ^ 2) :=
    V_intcast (a ^ 2 * (-1) ^ T + b ^ 2) (by push_cast; ring)
  have hV1 : V p (2 * (padicValNat p T : ℤ)) X1 := by
    simpa using V_mul hc1 (H_bound hp5 hT0)
  have hV2 : V p (2 * (padicValNat p T : ℤ)) X2 := by
    rcases Nat.even_or_odd T with hev | hodd
    · have hc2 : V p 0 ((a : ℚ) * b * (1 + (-1) ^ T)) :=
        V_intcast (a * b * 2) (by rw [hev.neg_one_pow]; push_cast; ring)
      simpa using V_mul hc2 (Hpm_bound hp5 hT0 (even_iff_two_dvd.mp hev))
    · rw [hX2, hodd.neg_one_pow]
      simp
  have hV : V p (2 * (padicValNat p T : ℤ)) (2 * (X1 - X2)) := by
    simpa using V_mul (V_nat (p := p) 2) (V_sub hV1 hV2)
  have hcoeff : coeff T (L p a b ^ 2) = 2 * (X1 - X2) / T :=
    eq_div_of_mul_eq hT (by rw [mul_comm]; exact h)
  rw [hcoeff]
  exact V_mono (V_div_nat hV hT0) (by omega)

end

end TF
