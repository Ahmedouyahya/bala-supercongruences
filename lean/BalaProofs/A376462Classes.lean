import BalaProofs.A376462Rep
import BalaProofs.A376462Kernel

/-!
# A376462, part 3: the four index classes (`proofs/A376462-first-congruence.md`, §1–§3)

For `N = m p^r`, `M = m p^(r-1)` (`p ≥ 5`, `m, r ≥ 1`; `p ∣ m` allowed):
* `T_scaled_int` (class (S), all `K, I`): `p^(3 + 3 v_p(M)) ∣ T(pM;pK,pI) - T(M;K,I)`.
* `classS`: `p^(3r) ∣ Σ_{K,I ≤ M} (T(N;pK,pI) - T(M;K,I))`.
* `classB`: `p^(3r) ∣ Σ'_k Σ'_i T(N;k,i)` (in fact `p^(4r)` termwise).
* `classK`: `p^(3r) ∣ Σ'_k Σ_{I ≤ M} T(N;k,pI)` (`= N² S_K`, `SK_dvd`).
* `classI`: `p^(3r) ∣ Σ_{K ≤ M} Σ'_i T(N;pK,i)` (`= N² S_I`, `SI_dvd`).
-/

open Nat Finset

namespace A376462Proof

/-- Graded product of six factors `X1² X2 X3² X4`. -/
lemma prod6_grad {R : Type*} [CommRing R] (q : R) (u w E e1 e2 e3 e4 : ℕ)
    (X1 X2 X3 X4 Y1 Y2 Y3 Y4 : R)
    (hX1 : q ^ u ∣ X1) (hY1 : q ^ u ∣ Y1) (hX3 : q ^ w ∣ X3) (hY3 : q ^ w ∣ Y3)
    (h1 : q ^ e1 ∣ Y1 - X1) (h2 : q ^ e2 ∣ Y2 - X2) (h3 : q ^ e3 ∣ Y3 - X3)
    (h4 : q ^ e4 ∣ Y4 - X4)
    (hE1 : E ≤ u + 2 * w + e1) (hE2 : E ≤ 2 * u + 2 * w + e2) (hE3 : E ≤ 2 * u + w + e3)
    (hE4 : E ≤ 2 * u + 2 * w + e4) :
    q ^ E ∣ Y1 ^ 2 * Y2 * Y3 ^ 2 * Y4 - X1 ^ 2 * X2 * X3 ^ 2 * X4 := by
  have sq : ∀ {x : R} {a : ℕ}, q ^ a ∣ x → q ^ (2 * a) ∣ x ^ 2 := fun h => by
    rw [pow_mul']
    exact pow_dvd_pow_of_dvd h 2
  have e : Y1 ^ 2 * Y2 * Y3 ^ 2 * Y4 - X1 ^ 2 * X2 * X3 ^ 2 * X4
      = (Y1 - X1) * (Y1 * Y3 ^ 2) * (Y2 * Y4) + (Y1 - X1) * (X1 * Y3 ^ 2) * (Y2 * Y4)
        + (Y2 - X2) * (X1 ^ 2 * Y3 ^ 2) * Y4 + (Y3 - X3) * (X1 ^ 2 * Y3) * (X2 * Y4)
        + (Y3 - X3) * (X1 ^ 2 * X3) * (X2 * Y4) + (Y4 - X4) * (X1 ^ 2 * X3 ^ 2) * X2 := by ring
  rw [e]
  have t1 : q ^ E ∣ (Y1 - X1) * (Y1 * Y3 ^ 2) :=
    (pow_dvd_pow q (by omega : E ≤ e1 + (u + 2 * w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h1 (mul_dvd_mul hY1 (sq hY3)))
  have t2 : q ^ E ∣ (Y1 - X1) * (X1 * Y3 ^ 2) :=
    (pow_dvd_pow q (by omega : E ≤ e1 + (u + 2 * w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h1 (mul_dvd_mul hX1 (sq hY3)))
  have t3 : q ^ E ∣ (Y2 - X2) * (X1 ^ 2 * Y3 ^ 2) :=
    (pow_dvd_pow q (by omega : E ≤ e2 + (2 * u + 2 * w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h2 (mul_dvd_mul (sq hX1) (sq hY3)))
  have t4 : q ^ E ∣ (Y3 - X3) * (X1 ^ 2 * Y3) :=
    (pow_dvd_pow q (by omega : E ≤ e3 + (2 * u + w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h3 (mul_dvd_mul (sq hX1) hY3))
  have t5 : q ^ E ∣ (Y3 - X3) * (X1 ^ 2 * X3) :=
    (pow_dvd_pow q (by omega : E ≤ e3 + (2 * u + w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h3 (mul_dvd_mul (sq hX1) hX3))
  have t6 : q ^ E ∣ (Y4 - X4) * (X1 ^ 2 * X3 ^ 2) :=
    (pow_dvd_pow q (by omega : E ≤ e4 + (2 * u + 2 * w))).trans
      (by rw [pow_add, pow_add]; exact mul_dvd_mul h4 (mul_dvd_mul (sq hX1) (sq hX3)))
  exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (t1.mul_right _) (t2.mul_right _))
    (t3.mul_right _)) (t4.mul_right _)) (t5.mul_right _)) (t6.mul_right _)

section padic

variable (p : ℕ) [Fact p.Prime]

/-- The valuation `β` attached to an index `K` at level `M`
(`min (v_p M) (v_p K)`, and `v_p M` for `K = 0`). -/
noncomputable def bet (M K : ℕ) : ℕ :=
  if K = 0 then M.factorization p else min (M.factorization p) (K.factorization p)

omit [Fact p.Prime] in
lemma bet_le (M K : ℕ) : bet p M K ≤ M.factorization p := by
  unfold bet
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

omit [Fact p.Prime] in
lemma bet_dvd (M K : ℕ) : p ^ bet p M K ∣ K := by
  unfold bet
  split_ifs with h
  · subst h
    exact dvd_zero _
  · exact (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd K p)

/-- `X1 = C(M,K)` carries `p^(v_p M - β)`. -/
lemma kazX (M K : ℕ) :
    (p : ℤ) ^ (M.factorization p - bet p M K) ∣ ((M.choose K : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    have hb : bet p M 0 = M.factorization p := by simp [bet]
    rw [hb, Nat.sub_self, pow_zero]
    exact one_dvd _
  have hb : bet p M K = min (M.factorization p) (K.factorization p) := by
    unfold bet
    rw [if_neg (by omega)]
  rcases le_or_gt K M with hKM | hKM
  · have hc := A386548.fact_le_choose p M K hK1 hKM
    have h1 : p ^ (M.factorization p - bet p M K) ∣ M.choose K :=
      (pow_dvd_pow p (by rw [hb]; omega)).trans (Nat.ordProj_dvd _ p)
    exact_mod_cast Int.natCast_dvd_natCast.mpr h1
  · rw [Nat.choose_eq_zero_of_lt hKM]
    simp

/-- Kazandzidis for `C(pM,pK)`. -/
lemma kaz1 (hp5 : 5 ≤ p) (M K : ℕ) (hM : 1 ≤ M) :
    (p : ℤ) ^ ((M.factorization p - bet p M K) + 3 + M.factorization p + 2 * bet p M K) ∣
      (((p * M).choose (p * K) : ℕ) : ℤ) - ((M.choose K : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    simp
  have hb : bet p M K = min (M.factorization p) (K.factorization p) := by
    unfold bet
    rw [if_neg (by omega)]
  rcases lt_trichotomy K M with hlt | heq | hgt
  · have h := OSS.kaz_int p hp5 M K
    have hc := A386548.fact_le_choose p M K hK1 hlt.le
    have hmin := OSS.fact_min_le_sub p M K hlt
    rw [hb]
    exact (pow_dvd_pow _ (by omega)).trans h
  · subst heq
    simp
  · rw [Nat.choose_eq_zero_of_lt hgt,
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hgt hp.pos)]
    simp

/-- Kazandzidis for `C(p(M+K),pK)`. -/
lemma kaz2 (hp5 : 5 ≤ p) (M K : ℕ) (hM : 1 ≤ M) :
    (p : ℤ) ^ (3 + M.factorization p + 2 * bet p M K) ∣
      (((p * (M + K)).choose (p * K) : ℕ) : ℤ) - (((M + K).choose K : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    simp
  have hb : bet p M K = min (M.factorization p) (K.factorization p) := by
    unfold bet
    rw [if_neg (by omega)]
  have h := OSS.kaz_int p hp5 (M + K) K
  rw [Nat.add_sub_cancel] at h
  have hmin := OSS.fact_min_le_add p M K (by omega)
  rw [hb]
  exact (pow_dvd_pow _ (by omega)).trans h

/-- Kazandzidis for `C(p(2M-K-I),pM)`. -/
lemma kaz4 (hp5 : 5 ≤ p) (M K I : ℕ) (hM : 1 ≤ M) :
    (p : ℤ) ^ (3 + M.factorization p + 2 * min (bet p M K) (bet p M I)) ∣
      (((p * (2 * M - K - I)).choose (p * M) : ℕ) : ℤ) - (((2 * M - K - I).choose M : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  set A := 2 * M - K - I with hA
  rcases lt_trichotomy M A with hlt | heq | hgt
  · have h := OSS.kaz_int p hp5 A M
    set μ := min (bet p M K) (bet p M I) with hμ
    have hμa : μ ≤ M.factorization p := (min_le_left _ _).trans (bet_le p M K)
    have hμK : p ^ μ ∣ K := (pow_dvd_pow p (min_le_left _ _)).trans (bet_dvd p M K)
    have hμI : p ^ μ ∣ I := (pow_dvd_pow p (min_le_right _ _)).trans (bet_dvd p M I)
    have hμM : p ^ μ ∣ M := (pow_dvd_pow p hμa).trans (Nat.ordProj_dvd M p)
    have hμA : p ^ μ ∣ A := Nat.dvd_sub (Nat.dvd_sub (hμM.mul_left 2) hμK) hμI
    have hμAM : p ^ μ ∣ A - M := Nat.dvd_sub hμA hμM
    have hvA : μ ≤ A.factorization p := (hp.pow_dvd_iff_le_factorization (by omega)).mp hμA
    have hvAM : μ ≤ (A - M).factorization p :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mp hμAM
    exact (pow_dvd_pow _ (by omega)).trans h
  · rw [← heq]
    simp
  · rw [Nat.choose_eq_zero_of_lt hgt,
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hgt hp.pos)]
    simp

/-- **Class (S)**, termwise: `p^(3 + 3 v_p(M)) ∣ T(pM;pK,pI) - T(M;K,I)` for all `K, I`. -/
lemma T_scaled_int (hp5 : 5 ≤ p) (M K I : ℕ) (hM : 1 ≤ M) :
    (p : ℤ) ^ (3 + 3 * M.factorization p) ∣ (T (p * M) (p * K) (p * I) : ℤ) - (T M K I : ℤ) := by
  have e1 : p * M + p * K = p * (M + K) := by ring
  have e2 : 2 * (p * M) - p * K - p * I = p * (2 * M - K - I) := by
    rw [Nat.mul_sub, Nat.mul_sub, show p * (2 * M) = 2 * (p * M) by ring]
  unfold T
  rw [e1, e2]
  push_cast
  have hX1 := kazX p M K
  have hX3 := kazX p M I
  have h1 := kaz1 p hp5 M K hM
  have h3 := kaz1 p hp5 M I hM
  have h2 := kaz2 p hp5 M K hM
  have h4 := kaz4 p hp5 M K I hM
  have hb := bet_le p M K
  have hg := bet_le p M I
  have hY1 : (p : ℤ) ^ (M.factorization p - bet p M K) ∣ (((p * M).choose (p * K) : ℕ) : ℤ) := by
    have e : (((p * M).choose (p * K) : ℕ) : ℤ) = ((M.choose K : ℕ) : ℤ)
        + ((((p * M).choose (p * K) : ℕ) : ℤ) - ((M.choose K : ℕ) : ℤ)) := by ring
    rw [e]
    exact dvd_add hX1 ((pow_dvd_pow _ (by omega)).trans h1)
  have hY3 : (p : ℤ) ^ (M.factorization p - bet p M I) ∣ (((p * M).choose (p * I) : ℕ) : ℤ) := by
    have e : (((p * M).choose (p * I) : ℕ) : ℤ) = ((M.choose I : ℕ) : ℤ)
        + ((((p * M).choose (p * I) : ℕ) : ℤ) - ((M.choose I : ℕ) : ℤ)) := by ring
    rw [e]
    exact dvd_add hX3 ((pow_dvd_pow _ (by omega)).trans h3)
  exact prod6_grad (p : ℤ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX1 hY1 hX3 hY3 h1 h2 h3 h4
    (by omega) (by omega) (by omega) (by omega)

/-- `C(N,k) = N k⁻¹ C(N-1,k-1)` in `ℤ_[p]` for `p ∤ k`. -/
lemma choose_unscaled (N k : ℕ) (hN : 1 ≤ N) (hk : ¬ p ∣ k) :
    ((N.choose k : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * (Ring.inverse (k : ℤ_[p]) * (((N - 1).choose (k - 1) : ℕ) : ℤ_[p])) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero p)
  have hu : IsUnit (k : ℤ_[p]) := Epoch361883.isUnit_nat_of_not_dvd p hk
  have hinv : (k : ℤ_[p]) * Ring.inverse (k : ℤ_[p]) = 1 := Ring.mul_inverse_cancel _ hu
  have h1 := choose_mul_self N k hN (by omega)
  have h1' : ((N.choose k : ℕ) : ℤ_[p]) * (k : ℤ_[p])
      = (N : ℤ_[p]) * (((N - 1).choose (k - 1) : ℕ) : ℤ_[p]) := by
    exact_mod_cast h1
  linear_combination (Ring.inverse (k : ℤ_[p])) * h1' - ((N.choose k : ℕ) : ℤ_[p]) * hinv

lemma T_unscaledK (N k I : ℕ) (hN : 1 ≤ N) (hk : ¬ p ∣ k) :
    ((T N k (p * I) : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) ^ 2 * (Ring.inverse (k : ℤ_[p]) ^ 2 * ((GK p N k I : ℕ) : ℤ_[p])) := by
  unfold T GK
  push_cast
  rw [choose_unscaled p N k hN hk]
  ring

lemma T_unscaledI (N i K : ℕ) (hN : 1 ≤ N) (hi : ¬ p ∣ i) :
    ((T N (p * K) i : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) ^ 2 * (Ring.inverse (i : ℤ_[p]) ^ 2 * ((GI p N i K : ℕ) : ℤ_[p])) := by
  unfold T GI
  push_cast
  rw [choose_unscaled p N i hN hi]
  ring

lemma classS (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ ∑ K ∈ range (m * p ^ (r - 1) + 1), ∑ I ∈ range (m * p ^ (r - 1) + 1),
      ((T (m * p ^ r) (p * K) (p * I) : ℤ) - (T (m * p ^ (r - 1)) K I : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hM : 1 ≤ m * p ^ (r - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hv : r - 1 ≤ (m * p ^ (r - 1)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mp (dvd_mul_left _ _)
  rw [lev p m r hr]
  apply Finset.dvd_sum
  intro K _
  apply Finset.dvd_sum
  intro I _
  exact (pow_dvd_pow _ (by omega)).trans (T_scaled_int p hp5 _ K I hM)

lemma classB (m r : ℕ) :
    (p : ℤ) ^ (3 * r) ∣ ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k),
      ∑ i ∈ (range (m * p ^ r + 1)).filter (fun i => ¬ p ∣ i), (T (m * p ^ r) k i : ℤ) := by
  apply Finset.dvd_sum
  intro k hk
  apply Finset.dvd_sum
  intro i hi
  have hk' := choose_dvd_of_not_dvd p (m * p ^ r) r k (dvd_mul_left _ _) (mem_filter.mp hk).2
  have hi' := choose_dvd_of_not_dvd p (m * p ^ r) r i (dvd_mul_left _ _) (mem_filter.mp hi).2
  have h4 : p ^ (4 * r) ∣ T (m * p ^ r) k i := by
    unfold T
    have e : p ^ (4 * r) = (p ^ r) ^ 2 * (p ^ r) ^ 2 := by ring
    rw [e]
    exact (mul_dvd_mul ((pow_dvd_pow_of_dvd hk' 2).mul_right _) (pow_dvd_pow_of_dvd hi' 2)).mul_right _
  have h3 : p ^ (3 * r) ∣ T (m * p ^ r) k i := (pow_dvd_pow p (by omega)).trans h4
  exact_mod_cast Int.natCast_dvd_natCast.mpr h3

lemma classK (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k),
      ∑ I ∈ range (m * p ^ (r - 1) + 1), (T (m * p ^ r) k (p * I) : ℤ) := by
  have hp : p.Prime := Fact.out
  have hN1 : 1 ≤ m * p ^ r :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) m
  rw [OSS.filter_range_succ_of_dvd p (m * p ^ r) hpN, A386548.int_dvd_iff_padic_dvd p]
  push_cast
  have e : ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      ∑ I ∈ range (m * p ^ (r - 1) + 1), ((T (m * p ^ r) k (p * I) : ℕ) : ℤ_[p])
      = ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2 * ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2
            * ∑ I ∈ range (m * p ^ (r - 1) + 1), ((GK p (m * p ^ r) k I : ℕ) : ℤ_[p]) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    exact T_unscaledK p (m * p ^ r) k I hN1 (mem_filter.mp hk).2
  rw [e]
  have hN2 : (p : ℤ_[p]) ^ (2 * r) ∣ ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2 := by
    have h : (p : ℤ_[p]) ^ r ∣ ((m * p ^ r : ℕ) : ℤ_[p]) :=
      (Epoch361883.nat_dvd_iff_padic_dvd p r _).mp (dvd_mul_left _ _)
    rw [show 2 * r = r * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h 2
  rw [show 3 * r = 2 * r + r by ring, pow_add]
  exact mul_dvd_mul hN2 (SK_dvd p hp5 m r hm hr)

lemma classI (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ ∑ K ∈ range (m * p ^ (r - 1) + 1),
      ∑ i ∈ (range (m * p ^ r + 1)).filter (fun i => ¬ p ∣ i), (T (m * p ^ r) (p * K) i : ℤ) := by
  have hp : p.Prime := Fact.out
  have hN1 : 1 ≤ m * p ^ r :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) m
  rw [Finset.sum_comm, OSS.filter_range_succ_of_dvd p (m * p ^ r) hpN,
    A386548.int_dvd_iff_padic_dvd p]
  push_cast
  have e : ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
      ∑ K ∈ range (m * p ^ (r - 1) + 1), ((T (m * p ^ r) (p * K) i : ℕ) : ℤ_[p])
      = ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2 * ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
          Ring.inverse (i : ℤ_[p]) ^ 2
            * ∑ K ∈ range (m * p ^ (r - 1) + 1), ((GI p (m * p ^ r) i K : ℕ) : ℤ_[p]) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K _
    exact T_unscaledI p (m * p ^ r) i K hN1 (mem_filter.mp hi).2
  rw [e]
  have hN2 : (p : ℤ_[p]) ^ (2 * r) ∣ ((m * p ^ r : ℕ) : ℤ_[p]) ^ 2 := by
    have h : (p : ℤ_[p]) ^ r ∣ ((m * p ^ r : ℕ) : ℤ_[p]) :=
      (Epoch361883.nat_dvd_iff_padic_dvd p r _).mp (dvd_mul_left _ _)
    rw [show 2 * r = r * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h 2
  rw [show 3 * r = 2 * r + r by ring, pow_add]
  exact mul_dvd_mul hN2 (SI_dvd p hp5 m r hm hr)

end padic

end A376462Proof
