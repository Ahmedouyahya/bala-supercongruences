import Mathlib
import BalaCheck.Old.UnitSquares

/-!
Lemma 3 of `notes/A361711-proof.md` (milestone M2):
for a prime `p ≥ 5`, `k ≥ 1`, `N = p^k`, `n = (N-1)/2` and
`U = {u ∈ [1, n] : p ∤ u}`, the sum of the squares of the inverses of the `u ∈ U`
modulo `N` vanishes modulo `N`.

Route: inversion permutes the units of `ZMod N` (sum over `(ZMod N)ˣ` reindexed by `x ↦ x⁻¹`),
so `Σ_{units} v⁻² = Σ_{units} v² = 0` (M1); the pairing `u ↦ N - u` identifies the full unit sum
with twice the half sum; `2` is a unit.
-/

open Finset

namespace Bala

/-- Reindexing a sum over the units of `ZMod (p^k)` as a sum over the natural numbers
`v < p^k` with `p ∤ v`. -/
theorem sum_units_eq (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) [NeZero (p ^ k)] {α : Type*}
    [AddCommMonoid α] (f : ZMod (p ^ k) → α) :
    ∑ x : (ZMod (p ^ k))ˣ, f x = ∑ v ∈ (range (p ^ k)).filter (fun v => ¬ p ∣ v), f v := by
  apply Finset.sum_bij (fun (x : (ZMod (p ^ k))ˣ) _ => (x : ZMod (p ^ k)).val)
  · intro x _
    simp only [mem_filter, mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hdvd
    have hcop := ZMod.val_coe_unit_coprime x
    have hp1 : p ∣ p ^ k := dvd_pow_self p (by omega)
    have h1 : Nat.Coprime (x : ZMod (p ^ k)).val p := Nat.Coprime.coprime_dvd_right hp1 hcop
    have h2 := Nat.Coprime.eq_one_of_dvd h1.symm hdvd
    exact hp.one_lt.ne' h2
  · intro x _ y _ hxy
    exact Units.ext (ZMod.val_injective _ hxy)
  · intro v hv
    simp only [mem_filter, mem_range] at hv
    have hcop : Nat.Coprime v (p ^ k) := by
      apply Nat.Coprime.pow_right
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hv.2).symm
    refine ⟨ZMod.unitOfCoprime v hcop, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hv.1]
  · intro x _
    rw [ZMod.natCast_zmod_val]

/-- the sum of the inverse squares over all units below `p^k` vanishes in `ZMod (p^k)` -/
theorem sum_inv_sq_units_zero (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ∑ v ∈ (range (p ^ k)).filter (fun v => ¬ p ∣ v), ((v : ZMod (p ^ k))⁻¹) ^ 2 = 0 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← sum_units_eq p k hp hk (fun x => (x⁻¹) ^ 2)]
  have h1 : ∑ x : (ZMod (p ^ k))ˣ, ((x : ZMod (p ^ k))⁻¹) ^ 2
      = ∑ x : (ZMod (p ^ k))ˣ, ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2 := by
    apply Fintype.sum_congr
    intro x
    rw [ZMod.inv_coe_unit]
  have h2 := Equiv.sum_comp (Equiv.inv (ZMod (p ^ k))ˣ)
    (fun x : (ZMod (p ^ k))ˣ => ((x : ZMod (p ^ k)) ^ 2))
  simp only [Equiv.inv_apply] at h2
  rw [h1, h2, sum_units_eq p k hp hk (fun x => x ^ 2)]
  have hdvd := pk_dvd_sum_unit_sq p k hp hp5 hk
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  push_cast at hz
  exact hz

/-- For a unit `a` of `ZMod N`, `((-a)⁻¹)^2 = (a⁻¹)^2`. -/
theorem neg_inv_sq {N : ℕ} (a : ZMod N) (ha : IsUnit a) : ((-a)⁻¹) ^ 2 = (a⁻¹) ^ 2 := by
  have h1 : (-a) * (-a)⁻¹ = 1 := ZMod.mul_inv_of_unit (-a) ha.neg
  have h2 : (-a) * (-(a⁻¹)) = 1 := by
    rw [neg_mul_neg]
    exact ZMod.mul_inv_of_unit a ha
  have h3 : (-a)⁻¹ = -(a⁻¹) := ha.neg.mul_left_cancel (h1.trans h2.symm)
  rw [h3, neg_sq]

/-- Lemma 3 in `ZMod (p^k)`: the half sum of inverse squares vanishes. -/
theorem sum_inv_sq_half_zero (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ∑ u ∈ (Icc 1 ((p ^ k - 1) / 2)).filter (fun u => ¬ p ∣ u), ((u : ZMod (p ^ k))⁻¹) ^ 2 = 0 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two (by omega)).pow
  obtain ⟨n, hn⟩ := hodd
  have hn' : (p ^ k - 1) / 2 = n := by omega
  rw [hn']
  have hpN : p ∣ p ^ k := dvd_pow_self p (by omega)
  -- the full sum, split at `n`
  have hV := sum_inv_sq_units_zero p k hp hp5 hk
  rw [← sum_filter_add_sum_filter_not ((range (p ^ k)).filter (fun v => ¬ p ∣ v))
    (fun v => v ≤ n)] at hV
  have hV1 : ((range (p ^ k)).filter (fun v => ¬ p ∣ v)).filter (fun v => v ≤ n)
      = (Icc 1 n).filter (fun u => ¬ p ∣ u) := by
    ext v
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, h3⟩, h2⟩
      rcases Nat.eq_zero_or_pos v with rfl | h
      · exact absurd (dvd_zero p) h2
      · exact h
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨by omega, h2⟩, h3⟩
  have hV2 : ((range (p ^ k)).filter (fun v => ¬ p ∣ v)).filter (fun v => ¬ v ≤ n)
      = ((Icc 1 n).filter (fun u => ¬ p ∣ u)).image (fun u => p ^ k - u) := by
    ext v
    simp only [mem_filter, mem_range, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨p ^ k - v, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd
      apply h2
      have : v = p ^ k - (p ^ k - v) := by omega
      rw [this]
      exact Nat.dvd_sub hpN hd
    · rintro ⟨u, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hd
      apply h3
      have : u = p ^ k - (p ^ k - u) := by omega
      rw [this]
      exact Nat.dvd_sub hpN hd
  rw [hV1, hV2] at hV
  have hinj : Set.InjOn (fun u => p ^ k - u) ↑((Icc 1 n).filter (fun u => ¬ p ∣ u)) := by
    intro x hx y hy hxy
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    omega
  rw [sum_image hinj] at hV
  have hsame : ∀ u ∈ (Icc 1 n).filter (fun u => ¬ p ∣ u),
      (((p ^ k - u : ℕ) : ZMod (p ^ k))⁻¹) ^ 2 = ((u : ZMod (p ^ k))⁻¹) ^ 2 := by
    intro u hu
    simp only [mem_filter, mem_Icc] at hu
    have hcop : Nat.Coprime u (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu.2).symm
    have hunit : IsUnit (u : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime u (p ^ k)).mpr hcop
    have hcast : ((p ^ k - u : ℕ) : ZMod (p ^ k)) = -(u : ZMod (p ^ k)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hcast]
    exact neg_inv_sq _ hunit
  rw [sum_congr rfl hsame] at hV
  -- hV : S + S = 0 ; 2 is a unit
  have h2unit : IsUnit (2 : ZMod (p ^ k)) := by
    have hcop : Nat.Coprime 2 (p ^ k) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have := (ZMod.isUnit_iff_coprime 2 (p ^ k)).mpr hcop
    simpa using this
  have h2 : (2 : ZMod (p ^ k)) * ∑ u ∈ (Icc 1 n).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ k))⁻¹) ^ 2 = 0 := by
    rw [two_mul]
    exact hV
  exact (h2unit.mul_right_eq_zero).mp h2

/-- Lemma 3, integer form (milestone M2): if `w u` is an inverse of `u` modulo `p^k` for every
`u ∈ U = {u ∈ [1, (p^k-1)/2] : p ∤ u}`, then `Σ_{u ∈ U} (w u)^2 ≡ 0 (mod p^k)`. -/
theorem sum_inv_sq_half_modEq (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (w : ℕ → ℤ)
    (hw : ∀ u ∈ (Icc 1 ((p ^ k - 1) / 2)).filter (fun u => ¬ p ∣ u),
      (u : ℤ) * w u ≡ 1 [ZMOD ((p ^ k : ℕ) : ℤ)]) :
    (∑ u ∈ (Icc 1 ((p ^ k - 1) / 2)).filter (fun u => ¬ p ∣ u), (w u) ^ 2)
      ≡ 0 [ZMOD ((p ^ k : ℕ) : ℤ)] := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hsame : ∀ u ∈ (Icc 1 ((p ^ k - 1) / 2)).filter (fun u => ¬ p ∣ u),
      ((w u : ℤ) : ZMod (p ^ k)) ^ 2 = ((u : ZMod (p ^ k))⁻¹) ^ 2 := by
    intro u hu
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hw u hu)
    push_cast at h
    simp only [mem_filter, mem_Icc] at hu
    have hcop : Nat.Coprime u (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu.2).symm
    have hunit : IsUnit (u : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime u (p ^ k)).mpr hcop
    have h1 : (u : ZMod (p ^ k)) * (u : ZMod (p ^ k))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
    rw [hunit.mul_left_cancel (h.trans h1.symm)]
  have hz := sum_inv_sq_half_zero p k hp hp5 hk
  rw [← sum_congr rfl hsame] at hz
  apply Int.modEq_zero_iff_dvd.mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  exact hz

end Bala
