import Mathlib
import Submission.Old.UnitProduct

/-!
# Block decomposition of the units below `m p^r`, and Lemmas A, B of
`notes/A364175-A364178-factorial-ratio-towers.md`

The units in `[0, m p^r)` are the `b p^r + v` with `b < m`, `v ∈ R_r`. Hence, in `ZMod (p^(3r))`
(`p ≥ 5`, `r ≥ 1`, `W = ∏_{v ∈ R_r} v`):

* Lemma A: `∏_{k < m p^r, p ∤ k} k = W^m`;
* Lemma B: `∏_{k < m p^r, p ∤ k} (d k + c p^r) = ∏_{k < m p^r, p ∤ k} (d k)` for a unit `d` and any `c`.
-/

open Finset

namespace Bala

/-- The units below `m p^r`, decomposed into `m` blocks `b p^r + R_r`. -/
theorem prod_units_blocks {M : Type*} [CommMonoid M] (p r m : ℕ) (hp : 0 < p) (hr : 1 ≤ r)
    (f : ℕ → M) :
    ∏ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k), f k
      = ∏ b ∈ range m, ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), f (b * p ^ r + v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← ih]
    simp only [prod_filter]
    rw [add_mul, one_mul, prod_range_add]
    congr 1
    apply prod_congr rfl
    intro v _
    have hdvd : p ∣ m * p ^ r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) m
    have hiff : p ∣ m * p ^ r + v ↔ p ∣ v := Nat.dvd_add_right hdvd
    simp only [hiff]

/-- Lemma A: `∏_{k < m p^r, p ∤ k} k = W^m` in `ZMod (p^(3r))`. -/
theorem prod_units_eq_pow (p r m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    ∏ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ (3 * r)))
      = (∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (v : ZMod (p ^ (3 * r)))) ^ m := by
  rw [prod_units_blocks p r m hp.pos hr]
  have hW : (∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (v : ZMod (p ^ (3 * r)))) ^ m
      = ∏ _b ∈ range m, ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
          (v : ZMod (p ^ (3 * r))) := by
    rw [prod_const, card_range]
  rw [hW]
  apply prod_congr rfl
  intro b _
  have h := prod_linear_block p r hp hp5 hr 1 (b : ZMod (p ^ (3 * r))) isUnit_one
  simp only [one_mul, one_pow] at h
  rw [← h]
  apply prod_congr rfl
  intro v _
  push_cast
  ring

/-- Lemma B: `∏_{k < m p^r, p ∤ k} (d k + c p^r) = ∏_{k < m p^r, p ∤ k} (d k)` for a unit `d`. -/
theorem prod_units_linear (p r m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (d c : ZMod (p ^ (3 * r))) (hd : IsUnit d) :
    ∏ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
        (d * (k : ZMod (p ^ (3 * r))) + c * (p : ZMod (p ^ (3 * r))) ^ r)
      = ∏ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k), (d * (k : ZMod (p ^ (3 * r)))) := by
  rw [prod_units_blocks p r m hp.pos hr, prod_units_blocks p r m hp.pos hr]
  apply prod_congr rfl
  intro b _
  have h1 := prod_linear_block p r hp hp5 hr d (d * b + c) hd
  have h2 := prod_linear_block p r hp hp5 hr d (d * b) hd
  rw [← h2] at h1
  have e1 : ∀ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      d * ((b * p ^ r + v : ℕ) : ZMod (p ^ (3 * r))) + c * (p : ZMod (p ^ (3 * r))) ^ r
        = d * (v : ZMod (p ^ (3 * r))) + (d * b + c) * (p : ZMod (p ^ (3 * r))) ^ r := by
    intro v _
    push_cast
    ring
  have e2 : ∀ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v),
      d * ((b * p ^ r + v : ℕ) : ZMod (p ^ (3 * r)))
        = d * (v : ZMod (p ^ (3 * r))) + (d * b) * (p : ZMod (p ^ (3 * r))) ^ r := by
    intro v _
    push_cast
    ring
  rw [prod_congr rfl e1, prod_congr rfl e2]
  exact h1

/-- `W` is a unit of `ZMod (p^(3r))`. -/
theorem isUnit_W (p r : ℕ) (hp : p.Prime) :
    IsUnit (∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (v : ZMod (p ^ (3 * r)))) := by
  have hc : Nat.Coprime (∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), v) (p ^ (3 * r)) := by
    apply Nat.Coprime.prod_left
    intro v hv
    exact coprime_pow_of_mem hp hv (3 * r)
  have := (ZMod.isUnit_iff_coprime _ _).mpr hc
  push_cast at this
  exact this

end Bala
