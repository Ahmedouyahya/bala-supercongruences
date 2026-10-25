import BalaCheck.TFHarmonic

/-!
# Theorem F at p = 3 (PLAN item 9): harmonic sums over units at p = 3

For `3 ∣ N`, `w = v_3(N)`:
* `S2_three`: `Σ_{k<N, 3∤k} 1/k² ≡ -N/3 (mod 3^w)` (Euler + Faulhaber + von Staudt at p = 3);
* `H_three`: `2 H_N ≡ N²/3 (mod 3^{2w})` (pairing `k ↔ N - k`), i.e. `H_N ≡ -3^{2w-1} (mod 3^{2w})`;
* `Hpm_three`: for `N` even, `H_N^± ≡ 0 (mod 3^{2w})` (via `alt_sum`).
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- Lemma E at p = 3 in the form used: `Σ_{k<N, 3∤k} 1/k² + N/3 ≡ 0 (mod 3^{v_3 N})`. -/
theorem S2_three {N : ℕ} (hN : N ≠ 0) (h3 : 3 ∣ N) :
    V 3 (padicValNat 3 N : ℤ)
      (∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), ((k : ℚ) ^ 2)⁻¹ + (N : ℚ) / 3) := by
  set w := padicValNat 3 N with hw
  have hw1 : 1 ≤ w := one_le_padicValNat_of_dvd hN h3
  obtain ⟨N', hN'⟩ := h3
  have hN'0 : N' ≠ 0 := by rintro rfl; simp at hN'; exact hN hN'
  have hvN' : padicValNat 3 N' + 1 = w := by
    rw [hw, hN', padicValNat.mul (by norm_num) hN'0, padicValNat.self (by norm_num)]
    ring
  set e := 2 * 3 ^ w - 2 with he
  have hlt := lt_pow_self' (p := 3) w
  have he2 : e + 2 = 2 * 3 ^ w := by omega
  have hew : w + 1 ≤ e := by omega
  have he0 : e ≠ 0 := by omega
  -- Step 1: per-term Euler congruence `1/k² ≡ k^e (mod 3^{w+1})`
  have step1 : ∀ k ∈ (range N).filter (fun k => ¬ 3 ∣ k),
      V 3 ((w : ℤ) + 1) (((k : ℚ) ^ 2)⁻¹ - (k : ℚ) ^ e) := by
    intro k hk
    obtain ⟨_, hkd⟩ := mem_filter.mp hk
    have hk0 : k ≠ 0 := by rintro rfl; exact hkd (dvd_zero 3)
    have hcop : Nat.Coprime k (3 ^ (w + 1)) :=
      Nat.Coprime.pow_right _
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hkd))
    have heuler := Nat.ModEq.pow_totient hcop
    have htot : Nat.totient (3 ^ (w + 1)) = 3 ^ w * 2 := by
      have h := Nat.totient_prime_pow Nat.prime_three (show 0 < w + 1 by omega)
      simpa using h
    rw [htot] at heuler
    have hdvd : (3 : ℤ) ^ (w + 1) ∣ ((k : ℤ) ^ (e + 2) - 1) := by
      have hd2 := heuler.symm.dvd
      push_cast at hd2
      rw [show e + 2 = 3 ^ w * 2 by rw [he2]; ring]
      exact_mod_cast hd2
    have hV : V 3 ((w : ℤ) + 1) ((k : ℚ) ^ (e + 2) - 1) := by
      have hcast : ((k : ℚ) ^ (e + 2) - 1) = ((((k : ℤ) ^ (e + 2) - 1 : ℤ)) : ℚ) := by
        push_cast; ring
      rw [hcast, show (w : ℤ) + 1 = ((w + 1 : ℕ) : ℤ) by push_cast; ring, V_int_iff_dvd]
      exact_mod_cast hdvd
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    have hk2 : ((k : ℚ) ^ 2) ≠ 0 := pow_ne_zero _ hkQ
    have hpow : ((k : ℚ) ^ 2)⁻¹ * (k : ℚ) ^ (e + 2) = (k : ℚ) ^ e := by
      rw [pow_add]
      calc ((k : ℚ) ^ 2)⁻¹ * ((k : ℚ) ^ e * (k : ℚ) ^ 2)
          = (k : ℚ) ^ e * (((k : ℚ) ^ 2)⁻¹ * (k : ℚ) ^ 2) := by ring
      _ = (k : ℚ) ^ e := by rw [inv_mul_cancel₀ hk2, mul_one]
    have hfact : ((k : ℚ) ^ 2)⁻¹ - (k : ℚ) ^ e = -(((k : ℚ) ^ 2)⁻¹ * ((k : ℚ) ^ (e + 2) - 1)) := by
      rw [mul_sub, hpow, mul_one, neg_sub]
    rw [hfact]
    apply V_neg
    have := V_mul (V_inv_pow_unit (p := 3) 2 hkd) hV
    simpa using this
  -- von Staudt at p = 3 for even `e`: `3 B_e + 1 ≡ 0 (mod 3)`
  have hB : V 3 1 ((3 : ℚ) * bernoulli e + 1) := by
    have h1 := V_pB_sub_S (p := 3) le_rfl e
    simp only [Nat.cast_ofNat] at h1
    have h2 : V 3 1 (∑ k ∈ range 3, (k : ℚ) ^ e + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, e = 2 * m := ⟨3 ^ w - 1, by omega⟩
      have hsum : ∑ k ∈ range 3, (k : ℚ) ^ e + 1 = (((4 ^ m + 2 : ℕ)) : ℚ) := by
        have h4 : (2 : ℚ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
        rw [hm]
        simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
          Nat.cast_ofNat, zero_add, one_pow, zero_pow (show 2 * m ≠ 0 by omega), h4]
        push_cast
        ring
      rw [hsum, show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, V_nat_iff_dvd, pow_one]
      have h4 : (4 : ℕ) ^ m % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      omega
    have := V_add h1 h2
    rwa [show (3 : ℚ) * bernoulli e - ∑ k ∈ range 3, (k : ℚ) ^ e
      + (∑ k ∈ range 3, (k : ℚ) ^ e + 1) = (3 : ℚ) * bernoulli e + 1 by ring] at this
  -- Step 2: `Σ_{k<N} k^e + N/3 ≡ 0 (mod 3^w)` (Faulhaber)
  have hS : V 3 (w : ℤ) (∑ k ∈ range N, (k : ℚ) ^ e + (N : ℚ) / 3) := by
    rw [faulhaber' N e, sum_range_succ, add_assoc]
    apply V_add
    · apply V_sum
      intro i hi
      have hie : i < e := mem_range.mp hi
      set d := e + 1 - i with hd
      have hd2 : 2 ≤ d := by omega
      have hterm : bernoulli i * (e.choose i : ℚ) * (N : ℚ) ^ d / ((d : ℕ) : ℚ)
          = ((bernoulli i * (e.choose i : ℚ)) * (N : ℚ) ^ d) * (1 / ((d : ℕ) : ℚ)) := by
        ring
      rw [hterm]
      have h1 : V 3 (-1 + 0) (bernoulli i * (e.choose i : ℚ)) :=
        V_mul (V_bernoulli i) (V_nat _)
      have hNd : V 3 ((d : ℕ) * (w : ℤ)) ((N : ℚ) ^ d) := V_pow (V_padicValNat hN) d
      have h2 := V_mul h1 hNd
      have h3 := V_mul h2 (V_inv_nat (p := 3) (n := d) (by omega))
      apply V_mono h3
      have h4 := padicValNat_add_two_le (p := 3) le_rfl hd2
      have h5 : padicValNat 3 d + 1 ≤ (d - 1) * w := by
        have := Nat.mul_le_mul (show padicValNat 3 d + 1 ≤ d - 1 by omega)
          (show 1 ≤ w by omega)
        omega
      have h5' : (padicValNat 3 d : ℤ) + 1 ≤ ((d : ℤ) - 1) * (w : ℤ) := by
        calc (padicValNat 3 d : ℤ) + 1 = ((padicValNat 3 d + 1 : ℕ) : ℤ) := by omega
        _ ≤ (((d - 1) * w : ℕ) : ℤ) := by exact_mod_cast h5
        _ = ((d : ℤ) - 1) * (w : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ d by omega)]
            norm_num
      linarith
    · rw [show e + 1 - e = 1 by omega]
      simp only [Nat.choose_self, Nat.cast_one, pow_one, mul_one, div_one]
      have hN3 : (N : ℚ) / 3 = (N' : ℚ) := by
        rw [hN']; push_cast; ring
      have heq : bernoulli e * (N : ℚ) + (N : ℚ) / 3 = (N' : ℚ) * ((3 : ℚ) * bernoulli e + 1) := by
        rw [hN']; push_cast; ring
      rw [heq]
      have h1 := V_mul (V_padicValNat (p := 3) hN'0) hB
      apply V_mono h1
      omega
  -- Step 3: remove the multiples of 3
  have hdil : ∑ k ∈ (range N).filter (fun k => 3 ∣ k), (k : ℚ) ^ e
      = (3 : ℚ) ^ e * ∑ j ∈ range N', (j : ℚ) ^ e := by
    rw [sum_filter, hN', sum_dilate₀ (by norm_num : (3 : ℕ) ≠ 0) N'
      (fun k => if 3 ∣ k then (k : ℚ) ^ e else 0) (fun j hj => if_neg hj), mul_sum]
    apply sum_congr rfl
    intro u _
    rw [if_pos (dvd_mul_right 3 u)]
    push_cast
    ring
  have hS' : V 3 (w : ℤ)
      (∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), (k : ℚ) ^ e + (N : ℚ) / 3) := by
    have hsplit := sum_filter_add_sum_filter_not (range N) (fun k => 3 ∣ k) (fun k => (k : ℚ) ^ e)
    have heq : ∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), (k : ℚ) ^ e + (N : ℚ) / 3
        = (∑ k ∈ range N, (k : ℚ) ^ e + (N : ℚ) / 3)
          - ∑ k ∈ (range N).filter (fun k => 3 ∣ k), (k : ℚ) ^ e := by
      rw [← hsplit]; ring
    rw [heq]
    apply V_sub hS
    rw [hdil]
    have h1 : V 3 (e : ℤ) ((3 : ℚ) ^ e) := by exact_mod_cast V_p_pow (p := 3) e
    have h2 : V 3 0 (∑ j ∈ range N', (j : ℚ) ^ e) := by
      apply V_sum; intro j _
      rw [show ((j : ℚ) ^ e) = (((j ^ e : ℕ)) : ℚ) by push_cast; ring]
      exact V_nat _
    have h3 := V_mul h1 h2
    apply V_mono h3
    omega
  have hfin : ∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), ((k : ℚ) ^ 2)⁻¹ + (N : ℚ) / 3
      = (∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), (((k : ℚ) ^ 2)⁻¹ - (k : ℚ) ^ e))
        + (∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), (k : ℚ) ^ e + (N : ℚ) / 3) := by
    rw [sum_sub_distrib]
    ring
  rw [hfin]
  exact V_add (V_mono (V_sum step1) (by omega)) hS'

/-- Lemma F(a) at p = 3: `2 H_N - N²/3 ≡ 0 (mod 3^{2 v_3 N})`. -/
theorem H_three {N : ℕ} (hN : N ≠ 0) (h3 : 3 ∣ N) :
    V 3 (2 * (padicValNat 3 N : ℤ)) (2 * ∑ i ∈ range N, hh 3 i - (N : ℚ) ^ 2 / 3) := by
  set w := padicValNat 3 N with hw
  have hw1 : 1 ≤ w := one_le_padicValNat_of_dvd hN h3
  have hfilt : ∑ i ∈ range N, hh 3 i = ∑ k ∈ (range N).filter (fun k => ¬ 3 ∣ k), ((k : ℚ))⁻¹ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    unfold hh
    rw [ite_not]
  rw [hfilt]
  have hS2 := S2_three hN h3
  set s := (range N).filter (fun k => ¬ 3 ∣ k) with hs
  have hmem : ∀ k ∈ s, k ≠ 0 ∧ k < N ∧ ¬ 3 ∣ k := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_filter.mp hk
    exact ⟨fun h => h2 (h ▸ dvd_zero 3), mem_range.mp h1, h2⟩
  have hstab : ∀ k ∈ s, N - k ∈ s := by
    intro k hk
    obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
    rw [hs, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    intro hc
    apply hkd
    have h := Nat.dvd_sub h3 hc
    rwa [show N - (N - k) = k by omega] at h
  have hrefl : ∑ k ∈ s, (((N - k : ℕ)) : ℚ)⁻¹ = ∑ k ∈ s, ((k : ℚ))⁻¹ := by
    apply sum_nbij' (fun k => N - k) (fun k => N - k)
    · exact hstab
    · exact hstab
    · intro k hk; obtain ⟨h1, h2, _⟩ := hmem k hk; omega
    · intro k hk; obtain ⟨h1, h2, _⟩ := hmem k hk; omega
    · intro k hk; rfl
  have h2H : (2 : ℚ) * ∑ k ∈ s, ((k : ℚ))⁻¹
      = ∑ k ∈ s, (((k : ℚ))⁻¹ + (((N - k : ℕ)) : ℚ)⁻¹) := by
    rw [sum_add_distrib, hrefl]
    ring
  have hpoint : ∀ k ∈ s, ((k : ℚ))⁻¹ + (((N - k : ℕ)) : ℚ)⁻¹
      = -((N : ℚ) * ((k : ℚ) ^ 2)⁻¹) - (N : ℚ) ^ 2 * ((k : ℚ) ^ 3)⁻¹
        - (N : ℚ) ^ 3 * (((k : ℚ) ^ 3 * ((k : ℚ) - (N : ℚ)))⁻¹) := by
    intro k hk
    obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    have hcast : (((N - k : ℕ)) : ℚ) = (N : ℚ) - (k : ℚ) := by
      rw [Nat.cast_sub hkN.le]
    have hNk : (N : ℚ) - (k : ℚ) ≠ 0 := by
      intro hc
      have hkN2 : (k : ℚ) = (N : ℚ) := by linarith
      have : k = N := by exact_mod_cast hkN2
      omega
    have hkN' : (k : ℚ) - (N : ℚ) ≠ 0 := by
      intro hc; apply hNk; linarith
    rw [hcast]
    field_simp
    ring
  have hS3 : V 3 0 (∑ k ∈ s, ((k : ℚ) ^ 3)⁻¹) := by
    apply V_sum
    intro k hk
    exact V_inv_pow_unit 3 (hmem k hk).2.2
  have hSmix : V 3 0 (∑ k ∈ s, (((k : ℚ) ^ 3 * ((k : ℚ) - (N : ℚ)))⁻¹)) := by
    apply V_sum
    intro k hk
    obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
    rw [mul_inv]
    have h1 := V_inv_pow_unit (p := 3) 3 hkd
    have h2 : V 3 0 (((k : ℚ) - (N : ℚ)))⁻¹ := by
      have hz : ((k : ℤ) - (N : ℤ)) ≠ 0 := by
        intro hc
        have : (k : ℤ) = (N : ℤ) := by omega
        have : k = N := by exact_mod_cast this
        omega
      have hd : ¬ (3 : ℤ) ∣ ((k : ℤ) - (N : ℤ)) := by
        intro hc
        apply hkd
        have hNd : (3 : ℤ) ∣ (N : ℤ) := by exact_mod_cast h3
        have : (3 : ℤ) ∣ (k : ℤ) := by
          have := dvd_add hc hNd
          rwa [sub_add_cancel] at this
        exact_mod_cast this
      have h3' := V_inv_int_unit (p := 3) hz (by exact_mod_cast hd)
      rwa [show (((k : ℤ) - (N : ℤ) : ℤ) : ℚ) = ((k : ℚ) - (N : ℚ)) by push_cast; ring] at h3'
    simpa using V_mul h1 h2
  have hkey : (2 : ℚ) * ∑ k ∈ s, ((k : ℚ))⁻¹ - (N : ℚ) ^ 2 / 3
      = -((N : ℚ) * (∑ k ∈ s, ((k : ℚ) ^ 2)⁻¹ + (N : ℚ) / 3))
        - (N : ℚ) ^ 2 * ∑ k ∈ s, ((k : ℚ) ^ 3)⁻¹
        - (N : ℚ) ^ 3 * ∑ k ∈ s, (((k : ℚ) ^ 3 * ((k : ℚ) - (N : ℚ)))⁻¹) := by
    rw [h2H, sum_congr rfl hpoint, sum_sub_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum,
      ← mul_sum, ← mul_sum]
    ring
  rw [hkey]
  have hNV := V_padicValNat (p := 3) hN
  apply V_sub
  apply V_sub
  · apply V_neg
    exact V_mono (V_mul hNV hS2) (by omega)
  · have h1 := V_mul (V_pow hNV 2) hS3
    apply V_mono h1
    simp only [Nat.cast_ofNat, add_zero]
    omega
  · have h1 := V_mul (V_pow hNV 3) hSmix
    apply V_mono h1
    simp only [Nat.cast_ofNat, add_zero]
    omega

/-- Lemma F(b) at p = 3: for even `N`, `H_N^± ≡ 0 (mod 3^{2 v_3 N})`. -/
theorem Hpm_three {N : ℕ} (hN : N ≠ 0) (h3 : 3 ∣ N) (h2 : 2 ∣ N) :
    V 3 (2 * (padicValNat 3 N : ℤ)) (∑ i ∈ range N, (-1 : ℚ) ^ (i + 1) * hh 3 i) := by
  obtain ⟨m, rfl⟩ := h2
  have hm : m ≠ 0 := by rintro rfl; simp at hN
  have hv : padicValNat 3 (2 * m) = padicValNat 3 m := by
    rw [padicValNat.mul two_ne_zero hm,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]
  have h3m : 3 ∣ m := by omega
  rw [alt_sum (p := 3) (by norm_num) m]
  have h1 := H_three hN h3
  have h2 := H_three hm h3m
  rw [hv] at h1 ⊢
  have hm2 : V 3 (2 * (padicValNat 3 m : ℤ)) ((m : ℚ) ^ 2) := by
    have := V_pow (V_padicValNat (p := 3) hm) 2
    apply V_mono this
    simp only [Nat.cast_ofNat]
    omega
  have hsum : V 3 (2 * (padicValNat 3 m : ℤ))
      ((2 : ℕ) * (∑ i ∈ range (2 * m), hh 3 i - ∑ k ∈ range m, hh 3 k)) := by
    have := V_add (V_sub h1 h2) hm2
    convert this using 1
    push_cast
    ring
  exact V_of_mul_nat_unit (p := 3) (c := 2) (by norm_num) hsum

end

end TF
