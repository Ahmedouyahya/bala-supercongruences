import Mathlib
import BalaProofs.UnitSquaresCore

/-!
Lemma 3 of `notes/A361711-proof.md`, integer core (milestone M1):
for a prime `p ≥ 5` and `k ≥ 1`, the sum of the squares of the unit residues modulo `p^k`
(represented by `v < p^k` with `¬ p ∣ v`) is divisible by `p^k`.
-/

open Finset

/-- `6 * Σ_{i < m+1} i^2 = m (m+1) (2m+1)` -/
theorem six_mul_sum_sq (m : ℕ) :
    6 * (∑ i ∈ range (m + 1), i ^ 2) = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

/-- The multiples of `p` below `p^k` (`k ≥ 1`) are exactly the `p * j` with `j < p^(k-1)`. -/
theorem filter_dvd_range_pow (p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    (range (p ^ k)).filter (fun v => p ∣ v) = (range (p ^ (k - 1))).image (fun j => p * j) := by
  have hpk : p ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  ext x
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hx, ⟨j, rfl⟩⟩
    refine ⟨j, ?_, rfl⟩
    rw [hpk] at hx
    exact Nat.lt_of_mul_lt_mul_left hx
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, dvd_mul_right p j⟩
    rw [hpk]
    exact Nat.mul_lt_mul_of_pos_left hj hp

/-- the sum of squares of the unit residues below `p^k`, as a difference of two full sums -/
theorem sum_unit_sq_eq (p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    (∑ v ∈ (range (p ^ k)).filter (fun v => ¬ p ∣ v), (v : ℤ) ^ 2)
      = (∑ i ∈ range (p ^ k), (i : ℤ) ^ 2)
        - (p : ℤ) ^ 2 * (∑ j ∈ range (p ^ (k - 1)), (j : ℤ) ^ 2) := by
  have hsplit := sum_filter_add_sum_filter_not (range (p ^ k)) (fun v => p ∣ v) (fun v => v ^ 2)
  have hinj : Set.InjOn (fun j => p * j) ↑(range (p ^ (k - 1))) := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  rw [filter_dvd_range_pow p k hp hk, sum_image hinj] at hsplit
  have h2 : ∑ x ∈ range (p ^ (k - 1)), (p * x) ^ 2 = p ^ 2 * ∑ j ∈ range (p ^ (k - 1)), j ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [h2] at hsplit
  have hc := congrArg (fun n : ℕ => (n : ℤ)) hsplit
  push_cast at hc ⊢
  linarith

/-- Main divisibility statement for `k ≥ 1` and `p ≥ 5` prime: `p^k ∣ Σ_{v < p^k, p ∤ v} v^2`. -/
theorem pk_dvd_sum_unit_sq (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    p ^ k ∣ ∑ v ∈ (range (p ^ k)).filter (fun v => ¬ p ∣ v), v ^ 2 := by
  have hp0 : 0 < p := hp.pos
  have hS := sum_unit_sq_eq p k hp0 hk
  have hq : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp0
  have hm : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp0
  have h1 : (6 : ℤ) * ∑ i ∈ range (p ^ k), (i : ℤ) ^ 2
      = ((p : ℤ) ^ k - 1) * (p : ℤ) ^ k * (2 * (p : ℤ) ^ k - 1) := by
    have h := six_mul_sum_sq (p ^ k - 1)
    rw [Nat.sub_add_cancel hq] at h
    have hc := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hq] at hc
    rw [hc]
    ring
  have h2 : (6 : ℤ) * ∑ j ∈ range (p ^ (k - 1)), (j : ℤ) ^ 2
      = ((p : ℤ) ^ (k - 1) - 1) * (p : ℤ) ^ (k - 1) * (2 * (p : ℤ) ^ (k - 1) - 1) := by
    have h := six_mul_sum_sq (p ^ (k - 1) - 1)
    rw [Nat.sub_add_cancel hm] at h
    have hc := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hm] at hc
    rw [hc]
    ring
  have hdvd : ((p ^ k : ℕ) : ℤ) ∣ ((∑ v ∈ (range (p ^ k)).filter (fun v => ¬ p ∣ v), v ^ 2 : ℕ) : ℤ) := by
    push_cast
    apply pk_dvd_core p k hp hp5 hk
    rw [hS]
    linear_combination h1 - (p : ℤ) ^ 2 * h2
  exact Int.natCast_dvd_natCast.mp hdvd
