import BalaProofs.A386548Series
import BalaProofs.A386548Padic

/-!
# Bala's supercongruence for A386548

The statement is taken from the Formal Conjectures file
`FormalConjectures/OEIS/Auto/386548_8788c4f8.lean` (commit 67338a1), imported unchanged: the final
theorem is stated as `type_of% @oeis_A386548_supercongruence_conjecture`.

Proof (`N = pM`): `a N = S N` (`A386548.a_eq_S`); split `S (pM)` into the indices `j = p i`
(paired with the level-`M` index `i`, `A386548.t_scaled`) and the indices `p ∤ j`
(each term divisible by `p^(2k)`, `A386548.t_unscaled`).
-/

open Finset

namespace A386548

/-- Step 2/3 (synchronisation + unscaled terms, in `ℕ`): if `2j + 3m = N`, `p^k ∣ N`, `p ∤ j`, then
`p^(2k) ∣ C(N,j) C(N+m-1,m)`. -/
lemma unscaled_nat (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N j m k : ℕ) (hk : p ^ k ∣ N)
    (hj : ¬ p ∣ j) (h : 2 * j + 3 * m = N) :
    p ^ (2 * k) ∣ N.choose j * (N + m - 1).choose m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p hk0.ne') hk
  have hm : ¬ p ∣ m := by
    intro hpm
    have h2j : p ∣ 2 * j := by
      have h1 : p ∣ 3 * m := dvd_mul_of_dvd_right hpm 3
      have e : 2 * j = N - 3 * m := by omega
      rw [e]; exact Nat.dvd_sub hpN h1
    rcases (Nat.Prime.dvd_mul hp).mp h2j with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · exact hj h2
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) hj
    · exact h0
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) hm
    · exact h0
  have hcj : Nat.Coprime (p ^ k) j :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hj)
  have hcm : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have h1 : p ^ k ∣ N.choose j := by
    have habs := Epoch361883.choose_absorb_low N j hj1 (by omega)
    have hd : p ^ k ∣ j * N.choose j := by rw [habs]; exact dvd_mul_of_dvd_left hk _
    exact hcj.dvd_of_dvd_mul_left hd
  have h2 : p ^ k ∣ (N + m - 1).choose m := by
    have habs := Nat.choose_succ_right_eq (N + m - 1) (m - 1)
    rw [Nat.sub_add_cancel hm1] at habs
    have e : N + m - 1 - (m - 1) = N := by omega
    rw [e] at habs
    have hd : p ^ k ∣ (N + m - 1).choose m * m := by rw [habs]; exact dvd_mul_of_dvd_right hk _
    exact hcm.dvd_of_dvd_mul_right hd
  rw [two_mul, pow_add]
  exact mul_dvd_mul h1 h2

/-- Unscaled summands of `S N`. -/
lemma t_unscaled (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N j k : ℕ) (hk : p ^ k ∣ N)
    (hj : ¬ p ∣ j) : (p : ℤ) ^ (2 * k) ∣ t N j := by
  unfold t
  split_ifs with hc
  · obtain ⟨hc1, c, hc2⟩ := hc
    have hm3 : 2 * j + 3 * ((N - 2 * j) / 3) = N := by omega
    have hnat := unscaled_nat p hp hp5 N j ((N - 2 * j) / 3) k hk hj hm3
    have hz : ((p : ℤ)) ^ (2 * k) ∣
        ((N.choose j : ℕ) : ℤ) * (((N + (N - 2 * j) / 3 - 1).choose ((N - 2 * j) / 3) : ℕ) : ℤ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr hnat
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right hz _
  · exact dvd_zero _

/-- Sign bookkeeping: `(-1)^(p i + p m) = (-1)^(i + m)` for odd `p`. -/
lemma sign_scaled (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (i m : ℕ) :
    (-1 : ℤ) ^ (p * i + p * m) = (-1 : ℤ) ^ (i + m) := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  rw [← mul_add, pow_mul, hodd.neg_one_pow]

/-- Step 4: scaled summands `t (pM) (pi)` against the level-`M` summand `t M i`. -/
lemma t_scaled (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M i : ℕ) :
    (p : ℤ) ^ (2 * M.factorization p + 3) ∣ t (p * M) (p * i) - t M i := by
  have hp : p.Prime := Fact.out
  have hpos : 0 < p := hp.pos
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  have hsub : p * M - 2 * (p * i) = p * (M - 2 * i) := by
    rw [Nat.mul_sub, show 2 * (p * i) = p * (2 * i) by ring]
  unfold t
  by_cases hc : 2 * i ≤ M ∧ 3 ∣ (M - 2 * i)
  · obtain ⟨hc1, m, hm⟩ := hc
    have hc' : 2 * (p * i) ≤ p * M ∧ 3 ∣ (p * M - 2 * (p * i)) := by
      refine ⟨?_, ?_⟩
      · rw [show 2 * (p * i) = p * (2 * i) by ring]; exact Nat.mul_le_mul_left p hc1
      · rw [hsub, hm]; exact ⟨p * m, by ring⟩
    rw [if_pos hc', if_pos ⟨hc1, ⟨m, hm⟩⟩]
    have e1 : (M - 2 * i) / 3 = m := by omega
    have e2 : (p * M - 2 * (p * i)) / 3 = p * m := by
      rw [hsub, hm, show p * (3 * m) = 3 * (p * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2, sign_scaled p hp hp5 i m]
    have e3 : p * M + p * m - 1 = p * (M + m) - 1 := by rw [mul_add]
    rw [e3]
    have key := scaled_int p hp5 M i m (by omega)
    have e4 : (-1 : ℤ) ^ (i + m) * (((p * M).choose (p * i) : ℕ) : ℤ)
          * (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ)
        - (-1 : ℤ) ^ (i + m) * ((M.choose i : ℕ) : ℤ) * (((M + m - 1).choose m : ℕ) : ℤ)
        = (-1 : ℤ) ^ (i + m) * ((((p * M).choose (p * i) : ℕ) : ℤ)
          * (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ)
          - ((M.choose i : ℕ) : ℤ) * (((M + m - 1).choose m : ℕ) : ℤ)) := by ring
    rw [e4]
    exact dvd_mul_of_dvd_right key _
  · have hc' : ¬ (2 * (p * i) ≤ p * M ∧ 3 ∣ (p * M - 2 * (p * i))) := by
      rintro ⟨h1, h2⟩
      apply hc
      refine ⟨?_, ?_⟩
      · rw [show 2 * (p * i) = p * (2 * i) by ring] at h1
        exact Nat.le_of_mul_le_mul_left h1 hpos
      · rw [hsub] at h2
        exact hcop.dvd_of_dvd_mul_left h2
    rw [if_neg hc', if_neg hc, sub_zero]
    exact dvd_zero _

/-- Splitting `S (pM)` into the indices divisible by `p` and the others. -/
lemma S_split (p M : ℕ) (hp : 0 < p) :
    S (p * M) = ∑ i ∈ range (M + 1), t (p * M) (p * i)
      + ∑ j ∈ (range (p * M + 1)).filter (fun j => ¬ p ∣ j), t (p * M) j := by
  unfold S
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * M + 1)) (fun j => p ∣ j)]
  congr 1
  have himg : (range (p * M + 1)).filter (fun j => p ∣ j) = (range (M + 1)).image (fun i => p * i) := by
    ext j
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hj, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hi
      have : p * (M + 1) ≤ p * i := Nat.mul_le_mul_left p (by omega)
      rw [mul_add, mul_one] at this
      omega
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, dvd_mul_right p i⟩
      have : p * i ≤ p * M := Nat.mul_le_mul_left p (by omega)
      omega
  rw [himg, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hp h

/-- Step 5: `p^(2k) ∣ S (pM) - S M` when `p^(k-1) ∣ M`, `k ≥ 1`, `M ≥ 1`. -/
lemma S_cong (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k)
    (hkM : p ^ (k - 1) ∣ M) : (p : ℤ) ^ (2 * k) ∣ S (p * M) - S M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hv : k - 1 ≤ M.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hkM
  have hkN : p ^ k ∣ p * M := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left p (by simpa using hkM)
  rw [S_split p M hp.pos, S]
  have e : ∑ i ∈ range (M + 1), t (p * M) (p * i)
        + ∑ j ∈ (range (p * M + 1)).filter (fun j => ¬ p ∣ j), t (p * M) j
        - ∑ i ∈ range (M + 1), t M i
      = ∑ i ∈ range (M + 1), (t (p * M) (p * i) - t M i)
        + ∑ j ∈ (range (p * M + 1)).filter (fun j => ¬ p ∣ j), t (p * M) j := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  apply dvd_add
  · apply Finset.dvd_sum
    intro i _
    exact dvd_trans (pow_dvd_pow _ (by omega)) (t_scaled p hp5 M i)
  · apply Finset.dvd_sum
    intro j hj
    exact t_unscaled p hp hp5 (p * M) j k hkN (Finset.mem_filter.mp hj).2

end A386548

