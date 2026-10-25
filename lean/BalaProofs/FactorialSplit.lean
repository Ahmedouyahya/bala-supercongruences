import Mathlib
import BalaProofs.ProductSplit

/-!
# Lemma C of `notes/A364175-A364178-factorial-ratio-towers.md` (Legendre-type splittings)

For `p ≥ 1` and `M ≥ 0`, with `U p Y := ∏_{k < Y, p ∤ k} k`:

* `(pM)! = p^M · M! · U p (pM)`;
* `∏_{j=1}^{pM} (u·pM + d·j) = p^M · ∏_{i=1}^{M} (u·M + d·i) · ∏_{j < pM, p ∤ j} (u·pM + d·j)`;
* `#{k < pM : p ∤ k} = pM − M`.
-/

open Finset

namespace Bala

/-- the product of the integers below `Y` that are prime to `p` -/
def U (p Y : ℕ) : ℕ := ∏ k ∈ (range Y).filter (fun k => ¬ p ∣ k), k

theorem prod_Icc_id_eq_factorial' (n : ℕ) : ∏ i ∈ Icc 1 n, i = n.factorial := by
  rw [prod_Icc_one_eq_prod_range (fun i => i) n]
  exact prod_range_add_one_eq_factorial n

theorem filter_not_dvd_Icc_eq_range (p M : ℕ) :
    (Icc 1 (p * M)).filter (fun k => ¬ p ∣ k) = (range (p * M)).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h3⟩
    rcases Nat.lt_or_ge k (p * M) with h | h
    · exact h
    · exfalso
      apply h3
      rw [le_antisymm h2 h]
      exact dvd_mul_right p M
  · rintro ⟨h1, h3⟩
    refine ⟨⟨?_, h1.le⟩, h3⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (dvd_zero p) h3
    · exact h

/-- Lemma C: `(pM)! = p^M · M! · U p (pM)`. -/
theorem factorial_mul_eq (p M : ℕ) (hp : 0 < p) :
    (p * M).factorial = p ^ M * M.factorial * U p (p * M) := by
  have hsplit : (∏ x ∈ (Icc 1 (p * M)).filter (fun k => p ∣ k), x)
      * ∏ x ∈ (Icc 1 (p * M)).filter (fun k => ¬ p ∣ k), x = ∏ x ∈ Icc 1 (p * M), x :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← prod_Icc_id_eq_factorial' (p * M), ← hsplit, filter_not_dvd_Icc_eq_range p M]
  unfold U
  congr 1
  have hf := filter_dvd_Icc p M 0 hp
  rw [add_zero] at hf
  rw [hf, prod_image]
  · rw [prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel, prod_Icc_id_eq_factorial']
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hp hxy

/-- the linear-form product, split into the multiples of `p` (which reproduce the lower level)
and the units -/
theorem prod_linear_split (p M u d : ℕ) (hp : 0 < p) :
    ∏ j ∈ Icc 1 (p * M), (u * (p * M) + d * j)
      = p ^ M * (∏ i ∈ Icc 1 M, (u * M + d * i))
        * ∏ j ∈ (range (p * M)).filter (fun j => ¬ p ∣ j), (u * (p * M) + d * j) := by
  have hsplit : (∏ j ∈ (Icc 1 (p * M)).filter (fun k => p ∣ k), (u * (p * M) + d * j))
      * ∏ j ∈ (Icc 1 (p * M)).filter (fun k => ¬ p ∣ k), (u * (p * M) + d * j)
      = ∏ j ∈ Icc 1 (p * M), (u * (p * M) + d * j) :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← hsplit, filter_not_dvd_Icc_eq_range p M]
  congr 1
  have hf := filter_dvd_Icc p M 0 hp
  rw [add_zero] at hf
  rw [hf, prod_image]
  · have h : ∀ i ∈ Icc 1 M, u * (p * M) + d * (p * i) = p * (u * M + d * i) := by
      intro i _
      ring
    rw [prod_congr rfl h, prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hp hxy

/-- the multiples of `p` below `pX` -/
theorem filter_dvd_range_mul (p X : ℕ) (hp : 0 < p) :
    (range (p * X)).filter (fun v => p ∣ v) = (range X).image (fun j => p * j) := by
  ext x
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hx, ⟨j, rfl⟩⟩
    exact ⟨j, Nat.lt_of_mul_lt_mul_left hx, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left hj hp, dvd_mul_right p j⟩

/-- `#{k < pX : p ∤ k} = pX − X` -/
theorem card_filter_not_dvd_range_mul (p X : ℕ) (hp : 0 < p) :
    ((range (p * X)).filter (fun v => ¬ p ∣ v)).card = p * X - X := by
  have h := card_filter_add_card_filter_not (s := range (p * X)) (fun v => p ∣ v)
  have hinj : Function.Injective (fun j => p * j) := fun a b hab => Nat.eq_of_mul_eq_mul_left hp hab
  rw [filter_dvd_range_mul p X hp, card_image_of_injective _ hinj, card_range, card_range] at h
  omega

theorem U_pos (p Y : ℕ) : 0 < U p Y := by
  unfold U
  apply prod_pos
  intro k hk
  simp only [mem_filter, mem_range] at hk
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exact absurd (dvd_zero p) hk.2
  · exact h

end Bala
