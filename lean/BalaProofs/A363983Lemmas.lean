import BalaProofs.OSSLib
import BalaProofs.A363983Rec

/-!
# A363983, part 2: the p-adic lemmas (`proofs/A363983.md`, §§2–3)

* `T_scaled_int` (Lemma 5, all scaled indices at once): for `M ≥ 1` and every `K`,
  `p^(3 + 3 v_p(M)) ∣ T(pM, pK) - T(M, K)`.
* `T_unscaled` (factorisation (2)): for `p ∤ k`, `T(N,k) = -(-1)^N N² k⁻² D(N, k-1, 2k)` in `ℤ_[p]`,
  with the lower-level kernel `D(n,k,j) = (-1)^k C(n-1,k) C(n+k,k) C(j,n)`.
* `D_level` (Lemmas 3–4 for `D`): `p^t ∣ D(m p^t, n, j) - D(m p^(t-1), ⌊n/p⌋, ⌊j/p⌋)`.
* `S_dvd` ((3) and Lemma 6, via `OSS.level_sum`): `p^r ∣ Σ'_{k < m p^r} k⁻² D(m p^r, k-1, 2k)`.
* `G0_dvd`: `p^(3r) ∣ Σ'_{k ≤ m p^r} T(m p^r, k)`.
-/

open Nat Finset

namespace A363983

/-- The lower-level kernel `D(n,k,j) = (-1)^k C(n-1,k) C(n+k,k) C(j,n)`. -/
def D (n0 n j : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (((n0 - 1).choose n : ℕ) : ℤ) * (((n0 + n).choose n : ℕ) : ℤ)
    * ((j.choose n0 : ℕ) : ℤ)

/-- Product of three congruences. -/
lemma prod3_dvd {R : Type*} [CommRing R] (d a1 a2 a3 b1 b2 b3 : R) (h1 : d ∣ a1 - b1)
    (h2 : d ∣ a2 - b2) (h3 : d ∣ a3 - b3) : d ∣ a1 * a2 * a3 - b1 * b2 * b3 := by
  have e : a1 * a2 * a3 - b1 * b2 * b3
      = (a1 - b1) * a2 * a3 + b1 * (a2 - b2) * a3 + b1 * b2 * (a3 - b3) := by ring
  rw [e]
  exact dvd_add (dvd_add ((h1.mul_right _).mul_right _) ((h2.mul_left _).mul_right _))
    (h3.mul_left _)

/-- Three factors with graded divisibility (used for Lemma 5). -/
lemma prod3_dvd_pow {R : Type*} [CommRing R] (q : R) (u E : ℕ) (X1 X2 X3 Y1 Y2 Y3 : R)
    (hY1 : q ^ u ∣ Y1) (hY2 : q ^ u ∣ Y2) (h1 : q ^ (u + E) ∣ X1 - Y1)
    (h2 : q ^ (u + E) ∣ X2 - Y2) (h3 : q ^ E ∣ X3 - Y3) :
    q ^ (2 * u + E) ∣ X1 * X2 * X3 - Y1 * Y2 * Y3 := by
  have hX2 : q ^ u ∣ X2 := by
    have : X2 = Y2 + (X2 - Y2) := by ring
    rw [this]; exact dvd_add hY2 ((pow_dvd_pow q (by omega)).trans h2)
  have e : X1 * X2 * X3 - Y1 * Y2 * Y3
      = (X1 - Y1) * X2 * X3 + Y1 * (X2 - Y2) * X3 + Y1 * Y2 * (X3 - Y3) := by ring
  rw [e]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · rw [show 2 * u + E = (u + E) + u by ring, pow_add]; exact (mul_dvd_mul h1 hX2).mul_right _
  · rw [show 2 * u + E = u + (u + E) by ring, pow_add]; exact (mul_dvd_mul hY1 h2).mul_right _
  · rw [show 2 * u + E = u + u + E by ring, pow_add, pow_add]
    exact mul_dvd_mul (mul_dvd_mul hY1 hY2) h3

section padic

variable (p : ℕ) [Fact p.Prime]

/- ### Lemma 5: scaled terms -/

/-- `v_p M ≤ v_p K + v_p C(M+K-1, K)` (from `K C(M+K-1,K) = M C(M+K-1,K-1)`). -/
lemma fact_le_choose_pred (M K : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) :
    M.factorization p ≤ K.factorization p + ((M + K - 1).choose K).factorization p := by
  have hp : p.Prime := Fact.out
  have hK0 : K ≠ 0 := by omega
  have hC0 : (M + K - 1).choose K ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hdvd : M ∣ K * (M + K - 1).choose K :=
    ⟨(M + K - 1).choose (K - 1), Epoch361883.key_ki M K hM hK⟩
  have hpw : p ^ M.factorization p ∣ K * (M + K - 1).choose K := (Nat.ordProj_dvd M p).trans hdvd
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (mul_ne_zero hK0 hC0)).mp hpw
  rwa [Nat.factorization_mul hK0 hC0, Finsupp.add_apply] at hle

lemma kaz1 (hp5 : 5 ≤ p) (M K : ℕ) (hK : 1 ≤ K) :
    (p : ℤ_[p]) ^ (3 + 2 * M.factorization p + K.factorization p) ∣
      (((p * M).choose (p * K) : ℕ) : ℤ_[p]) - ((M.choose K : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  rcases lt_trichotomy K M with hlt | heq | hgt
  · have h := OSS.kaz_padic p hp5 M K
    have hc := A386548.fact_le_choose p M K hK hlt.le
    have hmin := OSS.fact_min_le_sub p M K hlt
    exact (pow_dvd_pow _ (by omega)).trans h
  · subst heq; simp
  · rw [Nat.choose_eq_zero_of_lt hgt,
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hgt hp.pos)]
    simp

lemma kaz2 (hp5 : 5 ≤ p) (M K : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) :
    (p : ℤ_[p]) ^ (3 + 2 * M.factorization p + K.factorization p) ∣
      (((p * (M + K) - 1).choose (p * K) : ℕ) : ℤ_[p]) - (((M + K - 1).choose K : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hA := Epoch361883.stepA_At p (M + K) K hp.one_lt.le hK (by omega)
  have hB := Epoch361883.stepA_Bt (M + K) K hK (by omega)
  rw [Nat.add_sub_cancel] at hA hB
  have key : ((M + K : ℕ) : ℤ_[p]) * ((((p * (M + K) - 1).choose (p * K) : ℕ) : ℤ_[p])
        - (((M + K - 1).choose K : ℕ) : ℤ_[p]))
      = (M : ℤ_[p]) * ((((p * (M + K)).choose (p * K) : ℕ) : ℤ_[p])
        - (((M + K).choose K : ℕ) : ℤ_[p])) := by
    have hA' := congrArg (Nat.cast : ℕ → ℤ_[p]) hA
    have hB' := congrArg (Nat.cast : ℕ → ℤ_[p]) hB
    simp only [Nat.cast_mul] at hA' hB'
    rw [mul_sub, mul_sub, hA', hB']
  apply A386548.padic_cancel p (M + K) (by omega)
  rw [key]
  have hJ := OSS.kaz_padic p hp5 (M + K) K
  rw [Nat.add_sub_cancel] at hJ
  have hprod := mul_dvd_mul (A386548.padic_pow_fact_dvd p M) hJ
  rw [← pow_add] at hprod
  refine dvd_trans (pow_dvd_pow _ ?_) hprod
  omega

lemma kaz3 (hp5 : 5 ≤ p) (M K : ℕ) (hK : 1 ≤ K) :
    (p : ℤ_[p]) ^ (3 + M.factorization p + K.factorization p
        + min (M.factorization p) (K.factorization p)) ∣
      (((2 * (p * K)).choose (p * M) : ℕ) : ℤ_[p]) - (((2 * K).choose M : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  rw [show 2 * (p * K) = p * (2 * K) by ring]
  rcases lt_trichotomy M (2 * K) with hlt | heq | hgt
  · have h := OSS.kaz_padic p hp5 (2 * K) M
    have h2K : (2 * K).factorization p = (2 : ℕ).factorization p + K.factorization p := by
      rw [Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply]
    have hmin := OSS.fact_min_le_sub p (2 * K) M hlt
    exact (pow_dvd_pow _ (by omega)).trans h
  · rw [← heq]; simp
  · rw [Nat.choose_eq_zero_of_lt hgt,
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hgt hp.pos)]
    simp

lemma T_scaled_padic (hp5 : 5 ≤ p) (M K : ℕ) (hM : 1 ≤ M) :
    (p : ℤ_[p]) ^ (3 + 3 * M.factorization p) ∣
      ((T (p * M) (p * K) : ℤ) : ℤ_[p]) - ((T M K : ℤ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hpM : 0 < p * M := Nat.mul_pos hp.pos (by omega)
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have h1 : T (p * M) (p * 0) = 0 := by simp [T, Nat.choose_eq_zero_of_lt hpM]
    have h2 : T M 0 = 0 := by simp [T, Nat.choose_eq_zero_of_lt (by omega : 0 < M)]
    rw [h1, h2]; simp
  set a := M.factorization p with ha
  set b := K.factorization p with hb
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  have hsign : (-1 : ℤ_[p]) ^ (p * M + p * K) = (-1 : ℤ_[p]) ^ (M + K) := by
    rw [← mul_add, pow_mul, Odd.neg_one_pow hodd]
  simp only [T, Nat.pred_eq_sub_one]
  push_cast
  rw [hsign, show p * M + p * K - 1 = p * (M + K) - 1 by rw [mul_add], ← mul_sub]
  apply Dvd.dvd.mul_left
  have hY1 : (p : ℤ_[p]) ^ (a - b) ∣ ((M.choose K : ℕ) : ℤ_[p]) := by
    rcases le_or_gt K M with hle | hgt
    · have hc := A386548.fact_le_choose p M K hK hle
      exact (pow_dvd_pow _ (by omega)).trans (A386548.padic_pow_fact_dvd p _)
    · rw [Nat.choose_eq_zero_of_lt hgt]; simp
  have hY2 : (p : ℤ_[p]) ^ (a - b) ∣ (((M + K - 1).choose K : ℕ) : ℤ_[p]) := by
    have hc := fact_le_choose_pred p M K hM hK
    exact (pow_dvd_pow _ (by omega)).trans (A386548.padic_pow_fact_dvd p _)
  have h1 := kaz1 p hp5 M K hK
  have h2 := kaz2 p hp5 M K hM hK
  have h3 := kaz3 p hp5 M K hK
  have hE : 3 + 2 * a + b = (a - b) + (3 + a + b + min a b) := by omega
  rw [hE] at h1 h2
  have := prod3_dvd_pow (p : ℤ_[p]) (a - b) (3 + a + b + min a b) _ _ _ _ _ _ hY1 hY2 h1 h2 h3
  exact (pow_dvd_pow _ (by omega)).trans this

/-- **Lemma 5** (all scaled indices): `p^(3 + 3 v_p(M)) ∣ T(pM,pK) - T(M,K)`. -/
lemma T_scaled_int (hp5 : 5 ≤ p) (M K : ℕ) (hM : 1 ≤ M) :
    (p : ℤ) ^ (3 + 3 * M.factorization p) ∣ T (p * M) (p * K) - T M K := by
  rw [A386548.int_dvd_iff_padic_dvd p]
  push_cast
  exact T_scaled_padic p hp5 M K hM

/- ### (2): the unscaled terms -/

lemma T_unscaled (N k : ℕ) (hN : 1 ≤ N) (hk : ¬ p ∣ k) :
    ((T N k : ℤ) : ℤ_[p]) = -((-1 : ℤ_[p]) ^ N * (N : ℤ_[p]) ^ 2)
      * (Ring.inverse (k : ℤ_[p]) ^ 2 * ((D N (k - 1) (2 * k) : ℤ) : ℤ_[p])) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero p)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hu : IsUnit ((j + 1 : ℕ) : ℤ_[p]) := Epoch361883.isUnit_nat_of_not_dvd p hk
  have hinv : Ring.inverse ((j + 1 : ℕ) : ℤ_[p]) * ((j + 1 : ℕ) : ℤ_[p]) = 1 :=
    Ring.inverse_mul_cancel _ hu
  have h1 : ((N.choose (j + 1) : ℕ) : ℤ_[p]) * ((j + 1 : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * (((N - 1).choose j : ℕ) : ℤ_[p]) := by
    have := Nat.add_one_mul_choose_eq (N - 1) j
    rw [Nat.sub_add_cancel hN] at this
    exact_mod_cast this.symm
  have h2 : (((N + j).choose (j + 1) : ℕ) : ℤ_[p]) * ((j + 1 : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * (((N + j).choose j : ℕ) : ℤ_[p]) := by
    have := Epoch361883.key_ki N (j + 1) hN (by omega)
    rw [show N + (j + 1) - 1 = N + j by omega, Nat.add_sub_cancel] at this
    have h' : (N + j).choose (j + 1) * (j + 1) = N * (N + j).choose j := by
      rw [mul_comm]; exact this
    exact_mod_cast h'
  simp only [T, D, Nat.pred_eq_sub_one]
  rw [show N + (j + 1) - 1 = N + j by omega, Nat.add_sub_cancel]
  push_cast at h1 h2 hinv ⊢
  linear_combination
    ((-1 : ℤ_[p]) ^ N * (-1 : ℤ_[p]) ^ j * (((2 * (j + 1)).choose N : ℕ) : ℤ_[p])
      * ((N.choose (j + 1) : ℕ) : ℤ_[p]) * (((N + j).choose (j + 1) : ℕ) : ℤ_[p])
      * (1 + ((j : ℤ_[p]) + 1) * Ring.inverse ((j : ℤ_[p]) + 1))) * hinv
    - ((-1 : ℤ_[p]) ^ N * (-1 : ℤ_[p]) ^ j * (((2 * (j + 1)).choose N : ℕ) : ℤ_[p])
      * Ring.inverse ((j : ℤ_[p]) + 1) ^ 2 * (((N + j).choose (j + 1) : ℕ) : ℤ_[p])
      * ((j : ℤ_[p]) + 1)) * h1
    - ((-1 : ℤ_[p]) ^ N * (-1 : ℤ_[p]) ^ j * (((2 * (j + 1)).choose N : ℕ) : ℤ_[p])
      * Ring.inverse ((j : ℤ_[p]) + 1) ^ 2 * (N : ℤ_[p]) * (((N - 1).choose j : ℕ) : ℤ_[p])) * h2

/- ### Lemmas 3–4 for the kernel `D` -/

lemma D_level (m t n j : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ D (m * p ^ t) n j - D (m * p ^ (t - 1)) (n / p) (j / p) := by
  unfold D
  exact prod3_dvd _ _ _ _ _ _ _ (OSS.lemma3_int p m t n hm ht) (OSS.lemma4i_int p m t n ht)
    (OSS.lemma4ii_int p m t j ht)

/- ### (3) and Lemma 6 -/

lemma S_dvd (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2 * ((D (m * p ^ r) (k - 1) (2 * k) : ℤ) : ℤ_[p]) := by
  have hlev := OSS.level_sum p hp5 r m hr (fun t n j => D (m * p ^ t) n j)
    (fun t ht1 _ n j => D_level p m t n j hm ht1)
  have hdiff : (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2 * (((D (m * p ^ r) (k - 1) (2 * k)
        - D (m * p ^ (r - 1)) (k / p) (2 * k / p) : ℤ)) : ℤ_[p]) := by
    apply Finset.dvd_sum
    intro k hk
    have h := D_level p m r (k - 1) (2 * k) hm hr
    rw [OSS.pred_div_eq p k (mem_filter.mp hk).2] at h
    exact ((A386548.int_dvd_iff_padic_dvd p _ _).mp h).mul_left _
  have e : ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
        Ring.inverse (k : ℤ_[p]) ^ 2 * ((D (m * p ^ r) (k - 1) (2 * k) : ℤ) : ℤ_[p])
      = ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * ((D (m * p ^ (r - 1)) (k / p) (2 * k / p) : ℤ) : ℤ_[p])
        + ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * (((D (m * p ^ r) (k - 1) (2 * k)
            - D (m * p ^ (r - 1)) (k / p) (2 * k / p) : ℤ)) : ℤ_[p]) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [e]
  exact dvd_add hlev hdiff

/-- The unscaled part `G_0(N) = Σ'_{k ≤ N} T(N,k)` is divisible by `p^(3r)` for `N = m p^r`. -/
lemma G0_dvd (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k), T (m * p ^ r) k := by
  have hp : p.Prime := Fact.out
  have hN1 : 1 ≤ m * p ^ r :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) m
  rw [OSS.filter_range_succ_of_dvd p (m * p ^ r) hpN, A386548.int_dvd_iff_padic_dvd p]
  push_cast
  have e : ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k), ((T (m * p ^ r) k : ℤ) : ℤ_[p])
      = -((-1 : ℤ_[p]) ^ (m * p ^ r) * ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2)
        * ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * ((D (m * p ^ r) (k - 1) (2 * k) : ℤ) : ℤ_[p]) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact T_unscaled p (m * p ^ r) k hN1 (mem_filter.mp hk).2
  rw [e]
  have hN2 : (p : ℤ_[p]) ^ (2 * r) ∣ ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2 := by
    have h : (p : ℤ_[p]) ^ r ∣ ((m * p ^ r : ℕ) : ℤ_[p]) :=
      (Epoch361883.nat_dvd_iff_padic_dvd p r _).mp (dvd_mul_left _ _)
    rw [show 2 * r = r * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h 2
  rw [show 3 * r = 2 * r + r by ring, pow_add]
  exact mul_dvd_mul (dvd_neg.mpr (hN2.mul_left _)) (S_dvd p hp5 m r hm hr)

end padic

end A363983
