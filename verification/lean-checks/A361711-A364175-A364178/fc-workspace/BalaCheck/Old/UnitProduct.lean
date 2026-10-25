import Mathlib
import BalaCheck.Old.UnitSums

/-!
# The unit-product principle, core lemma

Lemma A/B of `notes/A364175-A364178-factorial-ratio-towers.md`, in one statement:
for a prime `p ≥ 5`, `r ≥ 1`, `R_r = {v < p^r : p ∤ v}`, and `e ∈ ZMod (p^(3r))`,

  `∏_{v ∈ R_r} (1 + e p^r v⁻¹) = 1`   in `ZMod (p^(3r))`.

Proof: with `ε_v = e p^r v⁻¹` all triple products vanish (`p^(3r) = 0`), so
`2 ∏ (1 + ε_v) = 2 + 2 e₁ + e₁² − Σ ε_v²`, and `e₁ = e p^r S₁ = 0`, `Σ ε_v² = e² p^(2r) S₂ = 0`
by the generalised Wolstenholme congruences of `UnitSums`; finally `2` is a unit.

Consequence (`prod_linear_block`): `∏_{v ∈ R_r} (d v + c p^r) = d^{|R_r|} ∏_{v ∈ R_r} v` for every
unit `d` and every `c`.
-/

open Finset

namespace Bala

/-- `2 ∏ (1 + ε u) = 2 + 2 Σ ε u + (Σ ε u)² − Σ (ε u)²` when all triple products vanish. -/
theorem two_mul_prod_one_add {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ε : ι → R) (h : ∀ u ∈ s, ∀ v ∈ s, ∀ w ∈ s, ε u * ε v * ε w = 0) :
    2 * ∏ u ∈ s, (1 + ε u)
      = 2 + 2 * (∑ u ∈ s, ε u) + (∑ u ∈ s, ε u) ^ 2 - ∑ u ∈ s, (ε u) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun u hu v hv w hw =>
      h u (mem_insert_of_mem hu) v (mem_insert_of_mem hv) w (mem_insert_of_mem hw))
    have h1 : ε a * (∑ u ∈ s, ε u) ^ 2 = 0 := by
      rw [sq, sum_mul_sum, mul_sum]
      apply sum_eq_zero
      intro u hu
      rw [mul_sum]
      apply sum_eq_zero
      intro v hv
      rw [← mul_assoc]
      exact h a (mem_insert_self a s) u (mem_insert_of_mem hu) v (mem_insert_of_mem hv)
    have h2 : ε a * ∑ u ∈ s, (ε u) ^ 2 = 0 := by
      rw [mul_sum]
      apply sum_eq_zero
      intro u hu
      rw [sq, ← mul_assoc]
      exact h a (mem_insert_self a s) u (mem_insert_of_mem hu) u (mem_insert_of_mem hu)
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    linear_combination (1 + ε a) * ih' + h1 - h2

/-- Core of the unit-product principle: `∏_{v ∈ R_r} (1 + e p^r v⁻¹) = 1` in `ZMod (p^(3r))`. -/
theorem prod_one_add_mul_inv (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (e : ZMod (p ^ (3 * r))) :
    ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      (1 + e * (p : ZMod (p ^ (3 * r))) ^ r * (v : ZMod (p ^ (3 * r)))⁻¹) = 1 := by
  have : NeZero (p ^ (3 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set S := (range (p ^ r)).filter (fun v => ¬ p ∣ v) with hS
  set P : ZMod (p ^ (3 * r)) := (p : ZMod (p ^ (3 * r))) ^ r with hP
  have hP3 : P ^ 3 = 0 := by
    have h0 : ((p ^ (3 * r) : ℕ) : ZMod (p ^ (3 * r))) = 0 := ZMod.natCast_self _
    push_cast at h0
    calc P ^ 3 = (p : ZMod (p ^ (3 * r))) ^ (3 * r) := by rw [hP]; ring
      _ = 0 := h0
  -- integer inverses modulo `p^(3r)`
  have hinv : ∀ v ∈ S, ∃ w : ℤ, (v : ℤ) * w ≡ 1 [ZMOD ((p ^ (3 * r) : ℕ) : ℤ)] := by
    intro v hv
    have hc : Nat.Coprime v (p ^ (3 * r)) := coprime_pow_of_mem hp hv (3 * r)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
    refine ⟨a, ?_⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨b, by linear_combination -hab⟩
  choose! w hw using hinv
  have hwcast : ∀ v ∈ S, ((w v : ℤ) : ZMod (p ^ (3 * r))) = (v : ZMod (p ^ (3 * r)))⁻¹ := by
    intro v hv
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hw v hv)
    push_cast at h
    have hunit := isUnit_of_mem hp hv (3 * r)
    have h1 : (v : ZMod (p ^ (3 * r))) * (v : ZMod (p ^ (3 * r)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    exact hunit.mul_left_cancel (h.trans h1.symm)
  -- `p^r S₁ = 0`
  have hS1 : P * ∑ v ∈ S, (v : ZMod (p ^ (3 * r)))⁻¹ = 0 := by
    have hw' : ∀ v ∈ S, (v : ℤ) * w v ≡ 1 [ZMOD ((p ^ (2 * r) : ℕ) : ℤ)] := fun v hv =>
      Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) (hw v hv)
    have h := sum_inv_units_modEq p r hp hp5 hr w hw'
    have hdvd : ((p ^ (3 * r) : ℕ) : ℤ) ∣ ((p ^ r : ℕ) : ℤ) * ∑ v ∈ S, w v := by
      have h1 := Int.modEq_zero_iff_dvd.mp h
      have h2 : ((p ^ (3 * r) : ℕ) : ℤ) = ((p ^ r : ℕ) : ℤ) * ((p ^ (2 * r) : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h2]
      exact mul_dvd_mul_left _ h1
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at h3
    rw [sum_congr rfl hwcast] at h3
    exact h3
  -- `p^(2r) S₂ = 0`
  have hS2 : P ^ 2 * ∑ v ∈ S, ((v : ZMod (p ^ (3 * r)))⁻¹) ^ 2 = 0 := by
    have hw' : ∀ v ∈ S, (v : ℤ) * w v ≡ 1 [ZMOD ((p ^ r : ℕ) : ℤ)] := fun v hv =>
      Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) (hw v hv)
    have h := sum_inv_sq_units_modEq p r hp hp5 hr w hw'
    have hdvd : ((p ^ (3 * r) : ℕ) : ℤ) ∣ ((p ^ r : ℕ) : ℤ) ^ 2 * ∑ v ∈ S, (w v) ^ 2 := by
      have h1 := Int.modEq_zero_iff_dvd.mp h
      have h2 : ((p ^ (3 * r) : ℕ) : ℤ) = ((p ^ r : ℕ) : ℤ) ^ 2 * ((p ^ r : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h2]
      exact mul_dvd_mul_left _ h1
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at h3
    have h4 : ∀ v ∈ S, ((w v : ℤ) : ZMod (p ^ (3 * r))) ^ 2
        = ((v : ZMod (p ^ (3 * r)))⁻¹) ^ 2 := by
      intro v hv
      rw [hwcast v hv]
    rw [sum_congr rfl h4] at h3
    exact h3
  -- the expansion
  have hε : ∀ u ∈ S, ∀ v ∈ S, ∀ x ∈ S,
      (e * P * (u : ZMod (p ^ (3 * r)))⁻¹) * (e * P * (v : ZMod (p ^ (3 * r)))⁻¹)
        * (e * P * (x : ZMod (p ^ (3 * r)))⁻¹) = 0 := by
    intro u _ v _ x _
    linear_combination (e ^ 3 * (u : ZMod (p ^ (3 * r)))⁻¹ * (v : ZMod (p ^ (3 * r)))⁻¹
      * (x : ZMod (p ^ (3 * r)))⁻¹) * hP3
  have hexp : 2 * ∏ v ∈ S, (1 + e * P * (v : ZMod (p ^ (3 * r)))⁻¹)
      = 2 + 2 * (∑ v ∈ S, e * P * (v : ZMod (p ^ (3 * r)))⁻¹)
        + (∑ v ∈ S, e * P * (v : ZMod (p ^ (3 * r)))⁻¹) ^ 2
        - ∑ v ∈ S, (e * P * (v : ZMod (p ^ (3 * r)))⁻¹) ^ 2 :=
    two_mul_prod_one_add S (fun v => e * P * (v : ZMod (p ^ (3 * r)))⁻¹) hε
  have hsum1 : ∑ v ∈ S, e * P * (v : ZMod (p ^ (3 * r)))⁻¹ = 0 := by
    rw [← mul_sum, mul_assoc, hS1, mul_zero]
  have hsum2 : ∑ v ∈ S, (e * P * (v : ZMod (p ^ (3 * r)))⁻¹) ^ 2 = 0 := by
    have h : ∀ v ∈ S, (e * P * (v : ZMod (p ^ (3 * r)))⁻¹) ^ 2
        = e ^ 2 * (P ^ 2 * ((v : ZMod (p ^ (3 * r)))⁻¹) ^ 2) := by
      intro v _
      ring
    rw [sum_congr rfl h, ← mul_sum, ← mul_sum, hS2, mul_zero]
  rw [hsum1, hsum2] at hexp
  have h2unit : IsUnit (2 : ZMod (p ^ (3 * r))) := by
    have hcop : Nat.Coprime 2 (p ^ (3 * r)) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have := (ZMod.isUnit_iff_coprime 2 (p ^ (3 * r))).mpr hcop
    simpa using this
  have hfin : (2 : ZMod (p ^ (3 * r))) * ∏ v ∈ S, (1 + e * P * (v : ZMod (p ^ (3 * r)))⁻¹)
      = 2 * 1 := by
    rw [hexp]
    ring
  exact h2unit.mul_left_cancel hfin

/-- `∏_{v ∈ R_r} (d v + c p^r) = d^{|R_r|} ∏_{v ∈ R_r} v` in `ZMod (p^(3r))`, for a unit `d`. -/
theorem prod_linear_block (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (d c : ZMod (p ^ (3 * r))) (hd : IsUnit d) :
    ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
        (d * (v : ZMod (p ^ (3 * r))) + c * (p : ZMod (p ^ (3 * r))) ^ r)
      = d ^ ((range (p ^ r)).filter (fun v => ¬ p ∣ v)).card
        * ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (v : ZMod (p ^ (3 * r))) := by
  have : NeZero (p ^ (3 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set S := (range (p ^ r)).filter (fun v => ¬ p ∣ v) with hS
  have hdd : d * d⁻¹ = 1 := ZMod.mul_inv_of_unit d hd
  have hfac : ∀ v ∈ S, d * (v : ZMod (p ^ (3 * r))) + c * (p : ZMod (p ^ (3 * r))) ^ r
      = (d * (v : ZMod (p ^ (3 * r))))
        * (1 + c * d⁻¹ * (p : ZMod (p ^ (3 * r))) ^ r * (v : ZMod (p ^ (3 * r)))⁻¹) := by
    intro v hv
    have hvv : (v : ZMod (p ^ (3 * r))) * (v : ZMod (p ^ (3 * r)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (isUnit_of_mem hp hv (3 * r))
    linear_combination
      (-(c * (p : ZMod (p ^ (3 * r))) ^ r
        * ((v : ZMod (p ^ (3 * r))) * (v : ZMod (p ^ (3 * r)))⁻¹))) * hdd
      + (-(c * (p : ZMod (p ^ (3 * r))) ^ r)) * hvv
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_mul_distrib, prod_const,
    prod_one_add_mul_inv p r hp hp5 hr (c * d⁻¹), mul_one]

end Bala
