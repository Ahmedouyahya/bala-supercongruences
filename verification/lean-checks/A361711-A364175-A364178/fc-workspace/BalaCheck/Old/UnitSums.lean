import Mathlib
import BalaCheck.Old.InvSquares

/-!
# Generalised Wolstenholme sums over the units below `p^r`

Lemma 2 of `notes/TheoremF-coefficient-framing-proof.md`, which is the arithmetic input of the
unit-product principle of `notes/A364175-A364178-factorial-ratio-towers.md`.
For a prime `p ≥ 5`, `r ≥ 1` and `R_r = {v < p^r : p ∤ v}`:

* `S₂ = Σ_{v ∈ R_r} v⁻² ≡ 0 (mod p^r)` — the integer form of `sum_inv_sq_units_zero` (`InvSquares`);
* `S₁ = Σ_{v ∈ R_r} v⁻¹ ≡ 0 (mod p^(2r))` — by the pairing `v ↦ p^r − v`: modulo `p^(2r)` one has
  `(p^r − v)⁻¹ = −v⁻¹ − p^r v⁻²`, hence `2 S₁ ≡ −p^r S₂ ≡ 0`.

Both statements are given for an arbitrary system `w : ℕ → ℤ` of integer inverses.
-/

open Finset

namespace Bala

theorem coprime_pow_of_mem {p r v : ℕ} (hp : p.Prime)
    (hv : v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v)) (k : ℕ) :
    Nat.Coprime v (p ^ k) := by
  simp only [mem_filter, mem_range] at hv
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hv.2).symm

theorem isUnit_of_mem {p r v : ℕ} (hp : p.Prime)
    (hv : v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v)) (k : ℕ) :
    IsUnit (v : ZMod (p ^ k)) :=
  (ZMod.isUnit_iff_coprime v (p ^ k)).mpr (coprime_pow_of_mem hp hv k)

/-- `S₂ ≡ 0 (mod p^r)`, integer form: if `w v` is an inverse of `v` modulo `p^r` for every
`v ∈ R_r`, then `Σ_{v ∈ R_r} (w v)^2 ≡ 0 (mod p^r)`. -/
theorem sum_inv_sq_units_modEq (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (w : ℕ → ℤ)
    (hw : ∀ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      (v : ℤ) * w v ≡ 1 [ZMOD ((p ^ r : ℕ) : ℤ)]) :
    (∑ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (w v) ^ 2) ≡ 0 [ZMOD ((p ^ r : ℕ) : ℤ)] := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hsame : ∀ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      ((w v : ℤ) : ZMod (p ^ r)) ^ 2 = ((v : ZMod (p ^ r))⁻¹) ^ 2 := by
    intro v hv
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hw v hv)
    push_cast at h
    have hunit : IsUnit (v : ZMod (p ^ r)) := isUnit_of_mem hp hv r
    have h1 : (v : ZMod (p ^ r)) * (v : ZMod (p ^ r))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
    rw [hunit.mul_left_cancel (h.trans h1.symm)]
  have hz := sum_inv_sq_units_zero p r hp hp5 hr
  rw [← sum_congr rfl hsame] at hz
  apply Int.modEq_zero_iff_dvd.mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  exact hz

/-- `S₁ ≡ 0 (mod p^(2r))`, integer form: if `w v` is an inverse of `v` modulo `p^(2r)` for every
`v ∈ R_r`, then `Σ_{v ∈ R_r} w v ≡ 0 (mod p^(2r))`. -/
theorem sum_inv_units_modEq (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (w : ℕ → ℤ)
    (hw : ∀ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      (v : ℤ) * w v ≡ 1 [ZMOD ((p ^ (2 * r) : ℕ) : ℤ)]) :
    (∑ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), w v) ≡ 0 [ZMOD ((p ^ (2 * r) : ℕ) : ℤ)] := by
  have : NeZero (p ^ (2 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set S := (range (p ^ r)).filter (fun v => ¬ p ∣ v) with hS
  have hpr : p ∣ p ^ r := dvd_pow_self p (by omega)
  -- the inverses in `ZMod (p^(2r))`
  have hinv : ∀ v ∈ S, (v : ZMod (p ^ (2 * r))) * ((w v : ℤ) : ZMod (p ^ (2 * r))) = 1 := by
    intro v hv
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hw v hv)
    push_cast at h
    exact h
  -- `(p^r)^2 = 0`
  have hp2 : ((p : ZMod (p ^ (2 * r))) ^ r) ^ 2 = 0 := by
    have h0 : ((p ^ (2 * r) : ℕ) : ZMod (p ^ (2 * r))) = 0 := ZMod.natCast_self _
    push_cast at h0
    calc ((p : ZMod (p ^ (2 * r))) ^ r) ^ 2 = (p : ZMod (p ^ (2 * r))) ^ (2 * r) := by ring
      _ = 0 := h0
  -- `v ↦ p^r - v` preserves `S`
  have hmem : ∀ v ∈ S, p ^ r - v ∈ S := by
    intro v hv
    simp only [hS, mem_filter, mem_range] at hv ⊢
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv.2 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hd
    apply hv.2
    have : v = p ^ r - (p ^ r - v) := by omega
    rw [this]
    exact Nat.dvd_sub hpr hd
  have hlt : ∀ v ∈ S, v < p ^ r := by
    intro v hv
    simp only [hS, mem_filter, mem_range] at hv
    exact hv.1
  -- the reflection formula `(p^r - v)⁻¹ = -v⁻¹ - p^r v⁻²`
  have hrefl : ∀ v ∈ S, ((w (p ^ r - v) : ℤ) : ZMod (p ^ (2 * r)))
      = -((w v : ℤ) : ZMod (p ^ (2 * r)))
        - (p : ZMod (p ^ (2 * r))) ^ r * ((w v : ℤ) : ZMod (p ^ (2 * r))) ^ 2 := by
    intro v hv
    have h1 := hinv v hv
    have h2 := hinv (p ^ r - v) (hmem v hv)
    have hcast : ((p ^ r - v : ℕ) : ZMod (p ^ (2 * r))) = (p : ZMod (p ^ (2 * r))) ^ r - v := by
      rw [Nat.cast_sub (hlt v hv).le]
      push_cast
      ring
    rw [hcast] at h2
    set x : ZMod (p ^ (2 * r)) := ((w v : ℤ) : ZMod (p ^ (2 * r))) with hx
    set y : ZMod (p ^ (2 * r)) := ((w (p ^ r - v) : ℤ) : ZMod (p ^ (2 * r))) with hy
    set P : ZMod (p ^ (2 * r)) := (p : ZMod (p ^ (2 * r))) ^ r with hP
    -- both `y` and `-x - P x^2` are inverses of `P - v`
    linear_combination (-(y) * (1 + P * x)) * h1 + (y * x ^ 2) * hp2 + (-x - P * x ^ 2) * h2
  -- reindex the sum by `v ↦ p^r - v`
  have hsum_refl : ∑ v ∈ S, ((w (p ^ r - v) : ℤ) : ZMod (p ^ (2 * r)))
      = ∑ v ∈ S, ((w v : ℤ) : ZMod (p ^ (2 * r))) := by
    apply Finset.sum_nbij' (fun v => p ^ r - v) (fun v => p ^ r - v)
    · intro v hv
      exact hmem v hv
    · intro v hv
      exact hmem v hv
    · intro v hv
      have := hlt v hv
      show p ^ r - (p ^ r - v) = v
      omega
    · intro v hv
      have := hlt v hv
      show p ^ r - (p ^ r - v) = v
      omega
    · intro v _
      rfl
  -- `2 Σ x = -p^r Σ x²`
  have hsum2 : (2 : ZMod (p ^ (2 * r))) * ∑ v ∈ S, ((w v : ℤ) : ZMod (p ^ (2 * r)))
      = -((p : ZMod (p ^ (2 * r))) ^ r * ∑ v ∈ S, ((w v : ℤ) : ZMod (p ^ (2 * r))) ^ 2) := by
    have h := hsum_refl
    rw [sum_congr rfl hrefl, sum_sub_distrib, sum_neg_distrib, ← mul_sum] at h
    linear_combination -h
  -- `p^r Σ x² = 0` from `S₂ ≡ 0 (mod p^r)`
  have hS2 : (p : ZMod (p ^ (2 * r))) ^ r * ∑ v ∈ S, ((w v : ℤ) : ZMod (p ^ (2 * r))) ^ 2 = 0 := by
    have hw' : ∀ v ∈ S, (v : ℤ) * w v ≡ 1 [ZMOD ((p ^ r : ℕ) : ℤ)] := by
      intro v hv
      exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) (hw v hv)
    have h := sum_inv_sq_units_modEq p r hp hp5 hr w hw'
    have hdvd : ((p ^ (2 * r) : ℕ) : ℤ) ∣ ((p ^ r : ℕ) : ℤ) * ∑ v ∈ S, (w v) ^ 2 := by
      have h1 := Int.modEq_zero_iff_dvd.mp h
      have h2 : ((p ^ (2 * r) : ℕ) : ℤ) = ((p ^ r : ℕ) : ℤ) * ((p ^ r : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h2]
      exact mul_dvd_mul_left _ h1
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at h3
    exact h3
  -- `2` is a unit
  have h2unit : IsUnit (2 : ZMod (p ^ (2 * r))) := by
    have hcop : Nat.Coprime 2 (p ^ (2 * r)) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have := (ZMod.isUnit_iff_coprime 2 (p ^ (2 * r))).mpr hcop
    simpa using this
  have hzero : ∑ v ∈ S, ((w v : ℤ) : ZMod (p ^ (2 * r))) = 0 := by
    have h := hsum2
    rw [hS2, neg_zero] at h
    exact (h2unit.mul_right_eq_zero).mp h
  apply Int.modEq_zero_iff_dvd.mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  exact hzero

end Bala
