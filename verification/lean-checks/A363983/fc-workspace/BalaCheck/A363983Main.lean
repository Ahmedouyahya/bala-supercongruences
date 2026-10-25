import BalaCheck.A363983Lemmas

/-!
# Bala's supercongruence for A363983

The statement is taken from the Formal Conjectures file
`FormalConjectures/OEIS/Auto/363983_3f7e4c53.lean` (commit 67338a1), imported unchanged: the final
theorem is stated as `type_of% @oeis_A363983_conjecture_supercongruence`.

Proof (`N = m p^r = pM`, `M = m p^(r-1)`): `A363983 n = s n` for `n ≥ 1` (`cast_A363983`, part 1);
split `s(pM)` into the indices `k = pj` (paired with the level-`M` index `j`, `T_scaled_int`,
modulus `p^(3 + 3 v_p M) ⊇ p^(3r)`) and the indices `p ∤ k` (`G0_dvd`, modulus `p^(3r)`).
-/

open Finset

namespace A363983

/-- `p^(3r) ∣ s(m p^r) - s(m p^(r-1))`. -/
theorem s_cong (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ s (m * p ^ r) - s (m * p ^ (r - 1)) := by
  haveI := Fact.mk hp
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hM : 1 ≤ m * p ^ r' :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hvM : r' ≤ (m * p ^ r').factorization p :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mp (dvd_mul_left _ _)
  have hN : m * p ^ (r' + 1) = p * (m * p ^ r') := by rw [pow_succ]; ring
  have hG := G0_dvd p hp5 m (r' + 1) hm (by omega)
  rw [hN] at hG ⊢
  unfold s
  rw [OSS.sum_split_dvd p (m * p ^ r') (T (p * (m * p ^ r')))]
  have hA : (p : ℤ) ^ (3 * (r' + 1)) ∣ ∑ j ∈ range (m * p ^ r' + 1), T (p * (m * p ^ r')) (p * j)
      - ∑ j ∈ range (m * p ^ r' + 1), T (m * p ^ r') j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro j _
    exact dvd_trans (pow_dvd_pow _ (by omega)) (T_scaled_int p hp5 (m * p ^ r') j hM)
  have e : ∑ j ∈ range (m * p ^ r' + 1), T (p * (m * p ^ r')) (p * j)
        + ∑ k ∈ (range (p * (m * p ^ r') + 1)).filter (fun k => ¬ p ∣ k), T (p * (m * p ^ r')) k
        - ∑ j ∈ range (m * p ^ r' + 1), T (m * p ^ r') j
      = (∑ j ∈ range (m * p ^ r' + 1), T (p * (m * p ^ r')) (p * j)
          - ∑ j ∈ range (m * p ^ r' + 1), T (m * p ^ r') j)
        + ∑ k ∈ (range (p * (m * p ^ r') + 1)).filter (fun k => ¬ p ∣ k), T (p * (m * p ^ r')) k := by
    ring
  rw [e]
  exact dvd_add hA hG

end A363983

theorem A363983_from_target : type_of% @oeis_A363983_conjecture_supercongruence := by
  intro p n r hp hp5 hn hr
  have hN : 1 ≤ n * p ^ r :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hM : 1 ≤ n * p ^ (r - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  rw [A363983.cast_A363983 _ hN, A363983.cast_A363983 _ hM]
  exact (Int.modEq_iff_dvd.mpr (A363983.s_cong p hp hp5 n r hn hr)).symm
