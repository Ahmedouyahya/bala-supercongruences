import BalaCheck.TF3G
import BalaCheck.TF3Exp

/-!
# Theorem F at p = 3 for `(a, b, c) = (2, -1, 1)` (PLAN items 7, 8, 10): Lemma A, Lemma J(b), assembly

* `lemmaA` (exact forms): `[y^M] Φ_M · y G' = -M [y^M] Φ_M (ψ - 1) G`, `ψ = y F'`;
* `Q_cong` (Lemma J(b)): every coefficient of `L - (ψ - 1) g` is `≡ 0 (mod 3)`;
* `theoremF3`: `v_3(A(3M) - A(M)) ≥ 3 (1 + v_3 M)` for `A = A 2 (-1) 1`;
* `tower_three`: the divisibility `3^{3k} ∣ s(n 3^k) - s(n 3^{k-1})` for `s` agreeing with `A 2 (-1) 1`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- `ψ = x φ'/φ = x F'`. -/
def psi (a b : ℤ) : ℚ⟦X⟧ := X * d⁄dX ℚ (F a b)

theorem coeff_X_deriv (G : ℚ⟦X⟧) (n : ℕ) : coeff n (X * d⁄dX ℚ G) = (n : ℚ) * coeff n G := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- Lemma A (exact forms), with `c = 1`. -/
theorem lemmaA (a b : ℤ) (M : ℕ) (G : ℚ⟦X⟧) :
    coeff M (Phi a b M * (X * d⁄dX ℚ G)) = -(M : ℚ) * coeff M (Phi a b M * ((psi a b - 1) * G)) := by
  have hD : d⁄dX ℚ (Phi a b M) = d⁄dX ℚ ((M : ℚ) • F a b) * Phi a b M :=
    ((isExpOf_iff_deriv _ _).mp (isExpOf_expS _)).2
  have hD' : d⁄dX ℚ ((M : ℚ) • F a b) = (M : ℚ) • d⁄dX ℚ (F a b) := Derivation.map_smul _ _ _
  have hkey : X * d⁄dX ℚ (Phi a b M * G)
      = C (M : ℚ) * (psi a b * (Phi a b M * G)) + Phi a b M * (X * d⁄dX ℚ G) := by
    rw [Derivation.leibniz, hD, hD', psi, smul_eq_mul, smul_eq_mul, smul_eq_C_mul]
    ring
  have hc := congrArg (coeff M) hkey
  rw [coeff_X_deriv, map_add, coeff_C_mul] at hc
  have e : Phi a b M * ((psi a b - 1) * G) = psi a b * (Phi a b M * G) - Phi a b M * G := by ring
  rw [e, map_sub]
  linear_combination (-1 : ℚ) * hc

theorem coeff_psi (n : ℕ) :
    coeff n (psi 2 (-1)) = if n = 0 then 0 else 2 * (-1) ^ (n + 1) + 1 := by
  rw [psi, coeff_X_deriv]
  simp only [F, coeff_mk, fc]
  split_ifs with h
  · simp
  · have hn : (n : ℚ) ≠ 0 := by exact_mod_cast h
    field_simp
    push_cast
    ring

theorem psi_rel : psi 2 (-1) * (1 - X ^ 2) = 3 * X - X ^ 2 := by
  ext n
  rw [mul_sub, mul_one, map_sub, map_sub, mul_comm, coeff_X_pow_mul', coeff_psi,
    show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm, coeff_C_mul, coeff_X, coeff_X_pow]
  rcases n with _ | _ | n
  · simp
  · norm_num [coeff_psi]
  · rw [if_pos (show 2 ≤ n + 1 + 1 by omega), show n + 1 + 1 - 2 = n by omega,
      if_neg (show n + 1 + 1 ≠ 1 by omega), coeff_psi,
      if_neg (show n + 1 + 1 ≠ 0 by omega)]
    rcases n with _ | n
    · norm_num
    · rw [if_neg (show n + 1 ≠ 0 by omega), if_neg (show n + 1 + 1 + 1 ≠ 2 by omega)]
      ring

/-- `u = 1/(1 - x²)`. -/
def uS : ℚ⟦X⟧ := expand 2 two_ne_zero c1S

theorem uS_rel : uS * (1 - X ^ 2) = 1 := by
  have h : expand 2 two_ne_zero (c1S * (1 - X)) = 1 := by
    rw [mul_comm, one_sub_X_mul_c1S, map_one]
  rw [map_mul, map_sub, map_one, expand_X] at h
  exact h

theorem coeff_uS (n : ℕ) : coeff n uS = if 2 ∣ n then 1 else 0 := by
  rw [uS, coeff_expand]
  split_ifs <;> simp [c1S]

theorem coeff_uS_sq (n : ℕ) : coeff n (uS ^ 2) = if 2 ∣ n then ((n / 2 + 1 : ℕ) : ℚ) else 0 := by
  rw [uS, ← map_pow, coeff_expand]
  split_ifs with h
  · rw [show c1S ^ 2 = c1S ^ (1 + 1) from rfl, coeff_c1S_pow, ← Nat.choose_symm_add,
      Nat.choose_one_right, add_comm]
  · rfl

theorem V3_three : V 3 1 (3 : ℚ) := by
  have h := V_p_pow (p := 3) 1
  simpa using h

/-- `L ≡ x² u² (mod 3)` coefficientwise. -/
theorem L_cong (n : ℕ) : V 3 1 (coeff n (L 3 2 (-1)) - coeff n (X ^ 2 * uS ^ 2)) := by
  rw [coeff_X_pow_mul', coeff_L]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [if_neg (by omega), sub_zero]
    interval_cases n
    · rw [Lc, if_pos (dvd_zero 3)]
      exact V_zero_val _
    · have h1 : Lc 3 2 (-1) 1 = 3 := by
        rw [Lc, if_neg (by norm_num), fc, if_neg (by norm_num)]
        norm_num
      rw [h1]
      exact V3_three
  · rw [if_pos hn, coeff_uS_sq]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    unfold Lc
    by_cases hm : 2 ∣ m
    · obtain ⟨k, rfl⟩ := hm
      rw [if_pos (dvd_mul_right 2 k), show 2 * k / 2 + 1 = k + 1 by omega]
      by_cases h3 : 3 ∣ 2 * k + 2
      · rw [if_pos h3, zero_sub]
        apply V_neg
        have h3k : 3 ^ 1 ∣ k + 1 := by rw [pow_one]; omega
        exact_mod_cast (V_nat_iff_dvd 1 (k + 1)).mpr h3k
      · rw [if_neg h3, fc, if_neg (by omega)]
        have hdvd : 3 ^ 1 ∣ 1 + 2 * (k + 1) ^ 2 := by
          rw [pow_one, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
          have hj : (k + 1) % 3 = 1 ∨ (k + 1) % 3 = 2 := by omega
          rcases hj with hj | hj <;> rw [hj]
        have hk0 : 2 * (k + 1) ≠ 0 := by omega
        have hk3 : ¬ 3 ∣ 2 * (k + 1) := by omega
        have hV := V_mul ((V_nat_iff_dvd (p := 3) 1 _).mpr hdvd) (V_inv_unit (p := 3) hk0 hk3)
        have hV' := V_neg (V_mono hV (show (1 : ℤ) ≤ ((1 : ℕ) : ℤ) + 0 by norm_num))
        have hs : (-1 : ℚ) ^ (2 * k + 2 + 1) = -1 := by
          rw [pow_succ, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
          norm_num
        convert hV' using 1
        rw [hs]
        have hkQ : ((k : ℚ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
    · rw [if_neg hm, sub_zero]
      by_cases h3 : 3 ∣ m + 2
      · rw [if_pos h3]
        exact V_zero_val _
      · rw [if_neg h3, fc, if_neg (by omega)]
        have hs : (-1 : ℚ) ^ (m + 2 + 1) = 1 := by
          obtain ⟨j, hj⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
          rw [show m + 2 + 1 = 2 * (j + 2) by omega, pow_mul]
          norm_num
        have hV := V_mul V3_three (V_inv_unit (p := 3) (show m + 2 ≠ 0 by omega) h3)
        convert V_mono hV (show (1 : ℤ) ≤ 1 + 0 by norm_num) using 1
        rw [hs]
        push_cast
        ring

/-- `g ≡ 2 x² u (mod 3)` coefficientwise. -/
theorem g_cong (n : ℕ) : V 3 1 (coeff n gS - coeff n (2 * (X ^ 2 * uS))) := by
  rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_X_pow_mul', gS,
    coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gc]
  · have hg := gc_cong (show n ≠ 0 by omega)
    have hrest : V 3 1 ((4 * (-1) ^ n + 1) - 2 * (if 2 ≤ n then coeff (n - 2) uS else 0)) := by
      rw [coeff_uS]
      rcases Nat.even_or_odd n with hev | hodd
      · obtain ⟨k, hk⟩ := hev
        rw [(show Even n from ⟨k, hk⟩).neg_one_pow, if_pos (by omega), if_pos (by omega)]
        norm_num
        exact V3_three
      · rw [hodd.neg_one_pow]
        obtain ⟨k, hk⟩ := hodd
        split_ifs with h1 h2
        · exfalso
          omega
        · norm_num
          exact V_neg V3_three
        · norm_num
          exact V_neg V3_three
    have := V_add hg hrest
    convert this using 1
    ring

theorem hat_identity :
    X ^ 2 * uS ^ 2 - (psi 2 (-1) - 1) * (2 * (X ^ 2 * uS))
      = 3 * (X ^ 2 * uS ^ 2 - 2 * X ^ 3 * uS ^ 2) := by
  linear_combination (-2 * X ^ 2 * uS * (1 - psi 2 (-1))) * uS_rel
    + (-2 * X ^ 2 * uS ^ 2) * psi_rel

theorem pint_psi_sub_one : PInt 3 (psi 2 (-1) - 1) := by
  intro j
  rw [map_sub, coeff_psi, coeff_one]
  split_ifs
  · exact V_intcast (-1) (by norm_num)
  · exact V_intcast (2 * (-1) ^ (j + 1) + 1) (by push_cast; ring)

theorem pint_uS : PInt 3 uS := by
  intro j
  rw [coeff_uS]
  split_ifs
  · exact V_one
  · exact V_zero_val _

theorem pint_two : PInt 3 (2 : ℚ⟦X⟧) := by
  rw [show (2 : ℚ⟦X⟧) = 1 + 1 by norm_num]
  exact pint_add pint_one pint_one

/-- Lemma J(b) for `(2, -1, 1)`: `L - (ψ - 1) g ≡ 0 (mod 3)` coefficientwise. -/
theorem Q_cong (n : ℕ) : V 3 1 (coeff n (L 3 2 (-1) - (psi 2 (-1) - 1) * gS)) := by
  have e : L 3 2 (-1) - (psi 2 (-1) - 1) * gS
      = (L 3 2 (-1) - X ^ 2 * uS ^ 2) - (psi 2 (-1) - 1) * (gS - 2 * (X ^ 2 * uS))
        + 3 * (X ^ 2 * uS ^ 2 - 2 * X ^ 3 * uS ^ 2) := by
    rw [← hat_identity]
    ring
  rw [e, map_add, map_sub, map_sub]
  apply V_add
  · apply V_sub (L_cong n)
    have h := V_coeff_mul (p := 3) (c := 0) (d := 1) pint_psi_sub_one
      (fun j => by rw [map_sub]; exact g_cong j) n
    exact V_mono h (by norm_num)
  · rw [show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm, coeff_C_mul]
    have hW : PInt 3 (X ^ 2 * uS ^ 2 - 2 * X ^ 3 * uS ^ 2) :=
      pint_sub (pint_mul (pint_pow pint_X 2) (pint_pow pint_uS 2))
        (pint_mul (pint_mul pint_two (pint_pow pint_X 3)) (pint_pow pint_uS 2))
    have h := V_mul V3_three (hW n)
    exact V_mono h (by norm_num)

/-- the remainder at `t`: the cubic correction plus the tail `ℓ ≥ 4` of `[x^{3t}] exp(N L)`. -/
def rho (M t : ℕ) : ℚ :=
  ((3 * M : ℕ) : ℚ) ^ 3 / 6 * (coeff (3 * t) (L 3 2 (-1) ^ 3) - coeff t (L 3 2 (-1)))
    + (coeff (3 * t) (E 3 2 (-1) (3 * M))
      - ((3 * M : ℕ) : ℚ) ^ 2 / 2 * coeff (3 * t) (L 3 2 (-1) ^ 2)
      - ((3 * M : ℕ) : ℚ) ^ 3 / 6 * coeff (3 * t) (L 3 2 (-1) ^ 3))

/-- Lemma C for the cubic weight: `v_3(N³/6) ≥ 3r - 1`. -/
theorem K_V (M : ℕ) : V 3 (3 * (1 + (padicValNat 3 M : ℤ)) - 1) (((3 * M : ℕ) : ℚ) ^ 3 / 6) := by
  have hdvd : 3 ^ (1 + padicValNat 3 M) ∣ 3 * M := by
    rw [pow_add, pow_one]
    exact mul_dvd_mul_left 3 pow_padicValNat_dvd
  have hNV : V 3 ((1 + padicValNat 3 M : ℕ) : ℤ) ((3 * M : ℕ) : ℚ) := (V_nat_iff_dvd _ _).mpr hdvd
  have h3 := V_div_nat (V_pow hNV 3) (show (6 : ℕ) ≠ 0 by norm_num)
  have h6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [h6] at h3
  simp only [Nat.cast_ofNat] at h3
  apply V_mono h3
  simp only [Nat.cast_add, Nat.cast_one]
  omega

theorem rho_V {M t : ℕ} (ht : t ≠ 0) : V 3 (3 * (1 + (padicValNat 3 M : ℤ))) (rho M t) := by
  unfold rho
  apply V_add
  · have h := V_mul (K_V M) (cubic_three 2 (-1) t)
    apply V_mono h
    omega
  · exact coeff_E_three 2 (-1) ht

/-- Proposition I (exact form): the expansion of `A(3M) - A(M)` with the quadratic term traded by
Lemma A for a multiple of `λ_M((ψ - 1) g)`. -/
theorem expansion (M : ℕ) :
    ∑ w ∈ range M, coeff (M * 3 - 3 * w) (E 3 2 (-1) (3 * M)) * coeff w (Phi 2 (-1) M)
      = ((3 * M : ℕ) : ℚ) ^ 3 / 6
          * coeff M (Phi 2 (-1) M * (L 3 2 (-1) - (psi 2 (-1) - 1) * gS))
        + ∑ w ∈ range M, coeff w (Phi 2 (-1) M) * rho M (M - w) := by
  have hconv : ∀ H : ℚ⟦X⟧, coeff 0 H = 0 →
      coeff M (Phi 2 (-1) M * H) = ∑ w ∈ range M, coeff w (Phi 2 (-1) M) * coeff (M - w) H := by
    intro H hH0
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
      Nat.sub_self, hH0, mul_zero, add_zero]
  have hA := lemmaA 2 (-1) M gS
  have hPQ : ((3 * M : ℕ) : ℚ) ^ 3 / 6
        * coeff M (Phi 2 (-1) M * (L 3 2 (-1) - (psi 2 (-1) - 1) * gS))
      = ((3 * M : ℕ) : ℚ) ^ 3 / 6 * coeff M (Phi 2 (-1) M * L 3 2 (-1))
        + ((3 * M : ℕ) : ℚ) ^ 2 / 2 * coeff M (Phi 2 (-1) M * (X * d⁄dX ℚ gS)) := by
    rw [mul_sub, map_sub, hA]
    push_cast
    ring
  rw [hPQ, hconv _ (coeff_L_dvd 2 (-1) (dvd_zero 3)), hconv _ (by rw [coeff_X_deriv]; simp),
    mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  rw [mem_range] at hw
  have ht : M - w ≠ 0 := by omega
  rw [show M * 3 - 3 * w = 3 * (M - w) by omega, coeff_X_deriv, gS, coeff_mk, gc_mul ht]
  unfold rho
  ring

/-- Theorem F₃(ii) for `(a, b, c) = (2, -1, 1)`. -/
theorem theoremF3 (M : ℕ) :
    V 3 (3 * (1 + (padicValNat 3 M : ℤ))) (A 2 (-1) 1 (3 * M) - A 2 (-1) 1 M) := by
  rw [A_sub (p := 3) (by norm_num), one_mul, expansion]
  apply V_add
  · have h := V_mul (K_V M) (V_coeff_mul (pint_Phi (p := 3) 2 (-1) M) Q_cong M)
    apply V_mono h
    omega
  · apply V_sum
    intro w hw
    rw [mem_range] at hw
    have h := V_mul (pint_Phi (p := 3) 2 (-1) M w) (rho_V (M := M) (show M - w ≠ 0 by omega))
    apply V_mono h
    omega

/-- Theorem F₃(ii) for `(2, -1, 1)` as a divisibility statement. -/
theorem tower_three (s : ℕ → ℕ) (hs : ∀ N, 1 ≤ N → (s N : ℚ) = A 2 (-1) 1 N) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (3 : ℤ) ^ (3 * k) ∣ (s (n * 3 ^ k) : ℤ) - (s (n * 3 ^ (k - 1)) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hM0 : n * 3 ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ (by norm_num))
  have hM1 : n * 3 ^ (j + 1) ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ (by norm_num))
  have hpM : n * 3 ^ (j + 1) = 3 * (n * 3 ^ j) := by ring
  have hF := theoremF3 (n * 3 ^ j)
  have hv : j ≤ padicValNat 3 (n * 3 ^ j) :=
    (padicValNat_dvd_iff_le hM0).mp (dvd_mul_left (3 ^ j) n)
  have hV : V 3 ((3 * (j + 1) : ℕ) : ℤ)
      ((s (n * 3 ^ (j + 1)) : ℚ) - (s (n * 3 ^ j) : ℚ)) := by
    rw [hs _ (Nat.one_le_iff_ne_zero.mpr hM1), hs _ (Nat.one_le_iff_ne_zero.mpr hM0), hpM]
    exact V_mono hF (by omega)
  have h := (V_int_iff_dvd (p := 3) (3 * (j + 1))
    ((s (n * 3 ^ (j + 1)) : ℤ) - (s (n * 3 ^ j) : ℤ))).mp
    (by rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]; exact hV)
  exact_mod_cast h

end

end TF
