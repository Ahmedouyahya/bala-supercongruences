import Submission.ShiftLibProd

/-!
# A376462 shifted congruence, lemma bank §2: harmonic block lemmas

Proof note: `proofs/A376462-shifted-congruence.md`, §2 (Lemmas 2.1–2.7).

* `blk p t l = B_t(l) = [l p^t, (l+1) p^t)`, `sig p t n = σ_t(n) = Σ′_{k ∈ B_t(n)} 1/k`.
* `eD p d = e(d)` (`0` if `(p-1) ∤ d`, else `1 + v_p(d)`).
* `cry p t a b δ = [ (a mod p^t) + (b mod p^t) + δ ≥ p^t ]` (carry indicator).
As in §1, `Ring.inverse` vanishes on multiples of `p`, so the sums below are the primed sums.
-/

open Nat Finset

namespace ShiftLib

section harm

variable (p : ℕ) [Fact p.Prime]

/-- The block `B_t(l) = {k : [k / p^t] = l}`. -/
def blk (t l : ℕ) : Finset ℕ := Ico (l * p ^ t) ((l + 1) * p ^ t)

/-- `σ_t(n) = Σ′_{k ∈ B_t(n)} 1/k`. -/
noncomputable def sig (t n : ℕ) : ℤ_[p] := ∑ k ∈ blk p t n, Ring.inverse (k : ℤ_[p])

/-- `e(d)` of Lemma 2.1. -/
def eD (d : ℕ) : ℕ := if (p - 1) ∣ d then 1 + padicValNat p d else 0

/-- Carry indicator `[ (a mod p^t) + (b mod p^t) + δ ≥ p^t ]`. -/
def cry (t a b δ : ℕ) : ℕ := if p ^ t ≤ a % p ^ t + b % p ^ t + δ then 1 else 0

/- ### Tools: blocks, `Ring.inverse` -/

omit [Fact p.Prime] in
lemma sum_blk {M : Type*} [AddCommMonoid M] (t l : ℕ) (f : ℕ → M) :
    ∑ k ∈ blk p t l, f k = ∑ σ ∈ range (p ^ t), f (l * p ^ t + σ) := by
  unfold blk
  rw [Finset.sum_Ico_eq_sum_range,
    show (l + 1) * p ^ t - l * p ^ t = p ^ t by rw [add_mul, one_mul, Nat.add_sub_cancel_left]]

omit [Fact p.Prime] in
lemma sum_range_blk {M : Type*} [AddCommMonoid M] (t b : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (b * p ^ t), f k = ∑ l ∈ range b, ∑ k ∈ blk p t l, f k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ← ih, sum_blk, show (b + 1) * p ^ t = b * p ^ t + p ^ t by ring,
      Finset.sum_range_add]

omit [Fact p.Prime] in
/-- `B_{t+u}(l) = ⋃_{n ∈ B_u(l)} B_t(n)`. -/
lemma blk_merge {M : Type*} [AddCommMonoid M] (t u l : ℕ) (f : ℕ → M) :
    ∑ n ∈ blk p u l, ∑ k ∈ blk p t n, f k = ∑ k ∈ blk p (t + u) l, f k := by
  rw [sum_blk p u l, sum_blk p (t + u) l]
  simp_rw [sum_blk p t]
  rw [pow_add, Epoch361883.sum_range_reindex (p ^ t) (p ^ u)]
  apply Finset.sum_congr rfl; intro σ _; apply Finset.sum_congr rfl; intro τ _
  congr 1; ring

omit [Fact p.Prime] in
lemma blk_zero (l : ℕ) : blk p 0 l = {l} := by
  unfold blk; rw [pow_zero, mul_one, mul_one]; exact Nat.Ico_succ_singleton l

lemma sig_zero (n : ℕ) : sig p 0 n = Ring.inverse (n : ℤ_[p]) := by
  unfold sig; rw [blk_zero, Finset.sum_singleton]

lemma sig_merge (s t i : ℕ) : ∑ n ∈ blk p t i, sig p s n = sig p (s + t) i := by
  unfold sig; exact blk_merge p s t i _

lemma inv_pow_eq_zero_of_dvd {k d : ℕ} (h : p ∣ k) (hd : 1 ≤ d) :
    Ring.inverse (k : ℤ_[p]) ^ d = 0 := by
  rw [inv_eq_zero_of_dvd p h]; exact zero_pow (by omega)

lemma two_isUnit (hp5 : 5 ≤ p) : IsUnit (2 : ℤ_[p]) := by
  have h : ¬ p ∣ 2 := by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have := Epoch361883.isUnit_nat_of_not_dvd p h
  simpa using this

lemma dvd_of_two_mul (hp5 : 5 ≤ p) {k : ℕ} {x : ℤ_[p]} (h : (p : ℤ_[p]) ^ k ∣ 2 * x) :
    (p : ℤ_[p]) ^ k ∣ x :=
  (IsUnit.dvd_mul_left (two_isUnit p hp5)).mp h

lemma H_succ (n : ℕ) : H p (n + 1) = H p n + Ring.inverse (((n + 1 : ℕ)) : ℤ_[p]) := by
  unfold H; rw [Finset.sum_range_succ]

lemma sum_range_inv_eq_H {N : ℕ} (hN : p ∣ N) :
    ∑ k ∈ range N, Ring.inverse (k : ℤ_[p]) = H p N := by
  unfold H; rw [Finset.sum_range_succ, inv_eq_zero_of_dvd p hN, add_zero]

lemma sum_range_inv_eq_H_pred {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range N, Ring.inverse (k : ℤ_[p]) = H p (N - 1) := by
  unfold H; rw [Nat.sub_add_cancel hN]

lemma ppow_dvd_natCast {v x : ℕ} (hx : p ^ v ∣ x) : (p : ℤ_[p]) ^ v ∣ (x : ℤ_[p]) := by
  obtain ⟨y, rfl⟩ := hx; exact ⟨y, by push_cast; ring⟩

/-- `1/k + 1/(N-k) = N/(k(N-k))` for `p ∣ N` (both sides `0` if `p ∣ k`). -/
lemma inv_add_inv_sub (N k : ℕ) (hN : p ∣ N) (hk : k ≤ N) :
    Ring.inverse (k : ℤ_[p]) + Ring.inverse ((N - k : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * (Ring.inverse (k : ℤ_[p]) * Ring.inverse ((N - k : ℕ) : ℤ_[p])) := by
  by_cases hpk : p ∣ k
  · have h2 : p ∣ N - k := Nat.dvd_sub hN hpk
    rw [inv_eq_zero_of_dvd p hpk, inv_eq_zero_of_dvd p h2]; ring
  · have h2 : ¬ p ∣ N - k := by
      intro h
      have := Nat.dvd_sub hN h
      rw [Nat.sub_sub_self hk] at this
      exact hpk this
    have h1 := mul_inv_nat p hpk
    have h3 := mul_inv_nat p h2
    have hc : ((N - k : ℕ) : ℤ_[p]) = (N : ℤ_[p]) - k := Nat.cast_sub hk
    rw [hc] at h3 ⊢
    linear_combination (-Ring.inverse (k : ℤ_[p])) * h3 - Ring.inverse ((N : ℤ_[p]) - k) * h1

/-- Exact second-order reflection: `1/(N-k) + 1/k + N/k² = N² /(k²(N-k))` for `p ∣ N`. -/
lemma inv_sub_expand (N k : ℕ) (hN : p ∣ N) (hk : k ≤ N) :
    Ring.inverse ((N - k : ℕ) : ℤ_[p]) + Ring.inverse (k : ℤ_[p])
        + (N : ℤ_[p]) * Ring.inverse (k : ℤ_[p]) ^ 2
      = (N : ℤ_[p]) ^ 2 * (Ring.inverse (k : ℤ_[p]) ^ 2 * Ring.inverse ((N - k : ℕ) : ℤ_[p])) := by
  have h := inv_add_inv_sub p N k hN hk
  linear_combination (1 + (N : ℤ_[p]) * Ring.inverse (k : ℤ_[p])) * h

/-- First-order shift: `1/(c+x) ≡ 1/x (mod p^t)` when `p^t ∣ c`. -/
lemma inv_shift (t c x : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ t ∣ Ring.inverse ((c + x : ℕ) : ℤ_[p]) - Ring.inverse (x : ℤ_[p]) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have hpc : p ∣ c := (dvd_pow_self p (by omega)).trans hc
  by_cases hpx : p ∣ x
  · rw [inv_eq_zero_of_dvd p hpx, inv_eq_zero_of_dvd p (dvd_add hpc hpx), sub_zero]
    exact dvd_zero _
  · have hpcx : ¬ p ∣ c + x := fun h => hpx ((Nat.dvd_add_right hpc).mp h)
    have h1 := mul_inv_nat p hpcx
    have h2 := mul_inv_nat p hpx
    push_cast at h1 ⊢
    have e : Ring.inverse ((c : ℤ_[p]) + x) - Ring.inverse (x : ℤ_[p])
        = -(c : ℤ_[p]) * (Ring.inverse ((c : ℤ_[p]) + x) * Ring.inverse (x : ℤ_[p])) := by
      linear_combination (-Ring.inverse ((c : ℤ_[p]) + x)) * h2 + Ring.inverse (x : ℤ_[p]) * h1
    rw [e]
    exact ((ppow_dvd_natCast p hc).neg_right).mul_right _

/-- Second-order shift: `1/(c+x) ≡ 1/x - c/x² (mod p^(2t))` when `p^t ∣ c`. -/
lemma inv_shift2 (t c x : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ (2 * t) ∣ Ring.inverse ((c + x : ℕ) : ℤ_[p]) - Ring.inverse (x : ℤ_[p])
      + (c : ℤ_[p]) * Ring.inverse (x : ℤ_[p]) ^ 2 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have hpc : p ∣ c := (dvd_pow_self p (by omega)).trans hc
  by_cases hpx : p ∣ x
  · rw [inv_eq_zero_of_dvd p hpx, inv_eq_zero_of_dvd p (dvd_add hpc hpx)]
    simp
  · have hpcx : ¬ p ∣ c + x := fun h => hpx ((Nat.dvd_add_right hpc).mp h)
    have h1 := mul_inv_nat p hpcx
    have h2 := mul_inv_nat p hpx
    push_cast at h1 ⊢
    set a := Ring.inverse ((c : ℤ_[p]) + x)
    set b := Ring.inverse (x : ℤ_[p])
    have e : a - b + (c : ℤ_[p]) * b ^ 2 = (c : ℤ_[p]) ^ 2 * (a * b ^ 2) := by
      linear_combination (b - (c : ℤ_[p]) * b ^ 2) * h1 + ((c : ℤ_[p]) * a * b - a) * h2
    rw [e, pow_mul']
    exact (pow_dvd_pow_of_dvd (ppow_dvd_natCast p hc) 2).mul_right _

/- ### Lemma 2.1, `d = 2` (from Epoch's block lemma) -/

/-- Lemma 2.1, `d = 2`, block form. -/
theorem invsq_blk (hp5 : 5 ≤ p) (v l : ℕ) :
    (p : ℤ_[p]) ^ v ∣ ∑ k ∈ blk p v l, Ring.inverse (k : ℤ_[p]) ^ 2 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  have h := OSS.inv_sq_blocks p hp5 v hv l
  rw [Finset.sum_filter_of_ne] at h
  · exact h
  · intro k _ hk hpk
    exact hk (inv_pow_eq_zero_of_dvd p hpk (by norm_num))

theorem invsq_range (hp5 : 5 ≤ p) (v y : ℕ) :
    (p : ℤ_[p]) ^ v ∣ ∑ k ∈ range (y * p ^ v), Ring.inverse (k : ℤ_[p]) ^ 2 := by
  rw [sum_range_blk]
  exact Finset.dvd_sum (fun l _ => invsq_blk p hp5 v l)

/-- Lemma 2.1, `d = 2`: `S₂(x) ≡ 0 (mod p^v)` when `p^v ∣ x`. -/
theorem S2_dvd' (hp5 : 5 ≤ p) (v x : ℕ) (hx : p ^ v ∣ x) : (p : ℤ_[p]) ^ v ∣ S p 2 x := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  obtain ⟨y, rfl⟩ := hx
  have hpx : p ∣ p ^ v * y := (dvd_pow_self p (by omega)).mul_right y
  unfold S
  rw [Finset.sum_range_succ, inv_pow_eq_zero_of_dvd p hpx (by norm_num), add_zero, mul_comm]
  exact invsq_range p hp5 v y

/-- Lemma 2.1, `d = 2`: `S₂(p^v y) ≡ 0 (mod p^v)`. -/
theorem S2_dvd (hp5 : 5 ≤ p) (v y : ℕ) : (p : ℤ_[p]) ^ v ∣ S p 2 (p ^ v * y) :=
  S2_dvd' p hp5 v _ (dvd_mul_right _ _)

/- ### Lemma 2.2 (block Wolstenholme) -/

/-- Lemma 2.2: `H′_x ≡ 0 (mod p^(2v))` whenever `p^v ∣ x`. -/
theorem H_dvd (hp5 : 5 ≤ p) (v x : ℕ) (hx : p ^ v ∣ x) : (p : ℤ_[p]) ^ (2 * v) ∣ H p x := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  have hpx : p ∣ x := (dvd_pow_self p (by omega)).trans hx
  have hrefl : H p x = ∑ k ∈ range (x + 1), Ring.inverse (((x - k : ℕ)) : ℤ_[p]) := by
    unfold H
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro k _
    rw [show x + 1 - 1 - k = x - k by omega]
  have h2 : 2 * H p x = (x : ℤ_[p]) * ∑ k ∈ range (x + 1),
      Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p]) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    unfold H
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk
    exact inv_add_inv_sub p x k hpx (by simp at hk; omega)
  have hS : (p : ℤ_[p]) ^ v ∣ ∑ k ∈ range (x + 1),
      Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p]) := by
    have hS2 := S2_dvd' p hp5 v x hx
    have hterm : (p : ℤ_[p]) ^ v ∣ ∑ k ∈ range (x + 1),
        (Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p])
          + Ring.inverse (k : ℤ_[p]) ^ 2) := by
      apply Finset.dvd_sum; intro k hk
      have e : Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p])
          + Ring.inverse (k : ℤ_[p]) ^ 2
          = Ring.inverse (k : ℤ_[p]) * (Ring.inverse (k : ℤ_[p])
            + Ring.inverse ((x - k : ℕ) : ℤ_[p])) := by ring
      rw [e, inv_add_inv_sub p x k hpx (by simp at hk; omega)]
      exact ((ppow_dvd_natCast p hx).mul_right _).mul_left _
    have e : ∑ k ∈ range (x + 1), Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p])
        = ∑ k ∈ range (x + 1), (Ring.inverse (k : ℤ_[p]) * Ring.inverse ((x - k : ℕ) : ℤ_[p])
          + Ring.inverse (k : ℤ_[p]) ^ 2) - S p 2 x := by
      unfold S; rw [Finset.sum_add_distrib]; ring
    rw [e]; exact dvd_sub hterm hS2
  have h3 : (p : ℤ_[p]) ^ (2 * v) ∣ 2 * H p x := by
    rw [h2, two_mul, pow_add]; exact mul_dvd_mul (ppow_dvd_natCast p hx) hS
  exact dvd_of_two_mul p hp5 h3

lemma sig_eq_H (t l : ℕ) (ht : 1 ≤ t) : sig p t l = H p ((l + 1) * p ^ t) - H p (l * p ^ t) := by
  have hpt : p ∣ p ^ t := dvd_pow_self p (by omega)
  unfold sig blk
  rw [Finset.sum_Ico_eq_sub _ (Nat.mul_le_mul_right _ (by omega)),
    sum_range_inv_eq_H p (hpt.mul_left _), sum_range_inv_eq_H p (hpt.mul_left _)]

/-- **Lemma 2.2**: `σ_t(l) ≡ 0 (mod p^(2t))`. -/
theorem sig_dvd (hp5 : 5 ≤ p) (t l : ℕ) : (p : ℤ_[p]) ^ (2 * t) ∣ sig p t l := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  rw [sig_eq_H p t l ht]
  exact dvd_sub (H_dvd p hp5 t _ (dvd_mul_left _ _)) (H_dvd p hp5 t _ (dvd_mul_left _ _))

/- ### Lemma 2.3 (reflection) -/

/-- Reflection core, `N = p^T`, `a ≤ N`:
`H′_{N-a} + Σ′_{a≤μ<N} 1/μ + N Σ′_{a≤μ<N} μ^{-2} ≡ 0 (mod p^(2T))`. -/
lemma refl_core (T a : ℕ) (hT : 1 ≤ T) (ha : a ≤ p ^ T) :
    (p : ℤ_[p]) ^ (2 * T) ∣ H p (p ^ T - a) + ∑ μ ∈ Ico a (p ^ T), Ring.inverse (μ : ℤ_[p])
      + (p : ℤ_[p]) ^ T * ∑ μ ∈ Ico a (p ^ T), Ring.inverse (μ : ℤ_[p]) ^ 2 := by
  set N := p ^ T with hN
  have hpN : p ∣ N := dvd_pow_self p (by omega)
  have hH : H p (N - a) = ∑ μ ∈ Ico a (N + 1), Ring.inverse ((N - μ : ℕ) : ℤ_[p]) := by
    unfold H
    rw [← Finset.sum_range_reflect, Finset.sum_Ico_eq_sum_range,
      show N + 1 - a = N - a + 1 by omega]
    apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    congr 2; omega
  have hI1 : ∑ μ ∈ Ico a (N + 1), Ring.inverse (μ : ℤ_[p])
      = ∑ μ ∈ Ico a N, Ring.inverse (μ : ℤ_[p]) := by
    rw [Finset.sum_Ico_succ_top ha, inv_eq_zero_of_dvd p hpN, add_zero]
  have hI2 : ∑ μ ∈ Ico a (N + 1), Ring.inverse (μ : ℤ_[p]) ^ 2
      = ∑ μ ∈ Ico a N, Ring.inverse (μ : ℤ_[p]) ^ 2 := by
    rw [Finset.sum_Ico_succ_top ha, inv_pow_eq_zero_of_dvd p hpN (by norm_num), add_zero]
  have hNc : (p : ℤ_[p]) ^ T = (N : ℤ_[p]) := by rw [hN]; push_cast; ring
  rw [hH, ← hI1, ← hI2, hNc, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.dvd_sum; intro μ hμ
  simp only [Finset.mem_Ico] at hμ
  rw [inv_sub_expand p N μ hpN (by omega), pow_mul', hNc]
  exact dvd_mul_right _ _

/-- **Lemma 2.3**: `H′_{p^t-1-n} - H′_n ≡ -p^t Σ′_{n<μ<p^t} μ^{-2} (mod p^(2t))`. -/
theorem refl (hp5 : 5 ≤ p) (t n : ℕ) (ht : 1 ≤ t) (hn : n < p ^ t) :
    (p : ℤ_[p]) ^ (2 * t) ∣ H p (p ^ t - 1 - n) - H p n
      + (p : ℤ_[p]) ^ t * ∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) ^ 2 := by
  have hpt : p ∣ p ^ t := dvd_pow_self p (by omega)
  have hc := refl_core p t (n + 1) ht (by omega)
  have hI : ∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) = H p (p ^ t) - H p n := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), sum_range_inv_eq_H p hpt]; rfl
  rw [hI, show p ^ t - (n + 1) = p ^ t - 1 - n by omega] at hc
  have hHN := H_dvd p hp5 t (p ^ t) dvd_rfl
  have e : H p (p ^ t - 1 - n) - H p n
      + (p : ℤ_[p]) ^ t * ∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) ^ 2
      = (H p (p ^ t - 1 - n) + (H p (p ^ t) - H p n)
        + (p : ℤ_[p]) ^ t * ∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) ^ 2)
        - H p (p ^ t) := by ring
  rw [e]; exact dvd_sub hc hHN

/-- Lemma 2.3: `H′_{p^t-1-n} ≡ H′_n (mod p^t)`. -/
theorem refl_weak (hp5 : 5 ≤ p) (t n : ℕ) (ht : 1 ≤ t) (hn : n < p ^ t) :
    (p : ℤ_[p]) ^ t ∣ H p (p ^ t - 1 - n) - H p n := by
  have h := refl p hp5 t n ht hn
  have h1 : (p : ℤ_[p]) ^ t ∣ H p (p ^ t - 1 - n) - H p n
      + (p : ℤ_[p]) ^ t * ∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) ^ 2 :=
    (pow_dvd_pow _ (by omega)).trans h
  have h2 := dvd_sub h1 (dvd_mul_right ((p : ℤ_[p]) ^ t)
    (∑ μ ∈ Ico (n + 1) (p ^ t), Ring.inverse (μ : ℤ_[p]) ^ 2))
  rwa [add_sub_cancel_right] at h2

/-- Lemma 2.3: `H′_{(p^t-k) p^s} ≡ H′_{k p^s} (mod p^(t+2s))` for `s, t ≥ 1`, `k ≤ p^t`. -/
theorem refl_scaled (hp5 : 5 ≤ p) (s t k : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hk : k ≤ p ^ t) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ H p ((p ^ t - k) * p ^ s) - H p (k * p ^ s) := by
  have hps : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hpts : p ^ (t + s) = p ^ t * p ^ s := pow_add p t s
  have hc := refl_core p (t + s) (k * p ^ s) (by omega)
    (by rw [hpts]; exact Nat.mul_le_mul_right _ hk)
  have hI : ∑ μ ∈ Ico (k * p ^ s) (p ^ (t + s)), Ring.inverse (μ : ℤ_[p])
      = H p (p ^ (t + s)) - H p (k * p ^ s) := by
    rw [Finset.sum_Ico_eq_sub _ (by rw [hpts]; exact Nat.mul_le_mul_right _ hk),
      sum_range_inv_eq_H p (dvd_pow_self p (by omega)), sum_range_inv_eq_H p (hps.mul_left _)]
  rw [hI, show p ^ (t + s) - k * p ^ s = (p ^ t - k) * p ^ s by rw [hpts, Nat.sub_mul]] at hc
  have hHN := H_dvd p hp5 (t + s) (p ^ (t + s)) dvd_rfl
  have hsq : (p : ℤ_[p]) ^ s ∣ ∑ μ ∈ Ico (k * p ^ s) (p ^ (t + s)), Ring.inverse (μ : ℤ_[p]) ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ (by rw [hpts]; exact Nat.mul_le_mul_right _ hk), hpts]
    exact dvd_sub (invsq_range p hp5 s (p ^ t)) (invsq_range p hp5 s k)
  have e : H p ((p ^ t - k) * p ^ s) - H p (k * p ^ s)
      = (H p ((p ^ t - k) * p ^ s) + (H p (p ^ (t + s)) - H p (k * p ^ s))
        + (p : ℤ_[p]) ^ (t + s) * ∑ μ ∈ Ico (k * p ^ s) (p ^ (t + s)), Ring.inverse (μ : ℤ_[p]) ^ 2)
        - H p (p ^ (t + s))
        - (p : ℤ_[p]) ^ (t + s) * ∑ μ ∈ Ico (k * p ^ s) (p ^ (t + s)), Ring.inverse (μ : ℤ_[p]) ^ 2 := by
    ring
  rw [e]
  refine dvd_sub (dvd_sub ((pow_dvd_pow _ (by omega)).trans hc) ((pow_dvd_pow _ (by omega)).trans hHN)) ?_
  rw [show t + 2 * s = (t + s) + s by ring, pow_add]
  exact mul_dvd_mul_left _ hsq

/- ### Lemma 2.4 (block shift) -/

/-- Lemma 2.4: `1/(c + λ)^d ≡ λ^{-d} (mod p^t)` when `p^t ∣ c`. -/
theorem inv_pow_shift (t c x d : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ t ∣ Ring.inverse ((c + x : ℕ) : ℤ_[p]) ^ d - Ring.inverse (x : ℤ_[p]) ^ d :=
  (inv_shift p t c x hc).trans (sub_dvd_pow_sub_pow _ _ d)

lemma H_add (c x : ℕ) :
    H p (c + x) = H p c + ∑ j ∈ range x, Ring.inverse ((c + (j + 1) : ℕ) : ℤ_[p]) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ← add_assoc (H p c), ← ih]
    exact H_succ p (c + x)

lemma H_eq_sum (x : ℕ) : H p x = ∑ j ∈ range x, Ring.inverse (((j + 1 : ℕ)) : ℤ_[p]) := by
  have h := H_add p 0 x
  simp only [Nat.zero_add] at h
  rw [h]; simp [H]

lemma S2_eq_sum (x : ℕ) : S p 2 x = ∑ j ∈ range x, Ring.inverse (((j + 1 : ℕ)) : ℤ_[p]) ^ 2 := by
  unfold S; rw [Finset.sum_range_succ']; simp

/-- **Lemma 2.4**: `H′_{c+x} ≡ H′_c + H′_x (mod p^t)` when `p^t ∣ c` (e.g. `c = i p^t`). -/
theorem H_shift (t c x : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ t ∣ H p (c + x) - H p c - H p x := by
  rw [H_add, H_eq_sum p x, add_sub_cancel_left, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum; intro j _
  rw [show c + (j + 1) = c + (j + 1) from rfl]
  exact inv_shift p t c (j + 1) hc

/-- Second-order block shift: `H′_{c+x} ≡ H′_c + H′_x - c S₂(x) (mod p^(2t))` when `p^t ∣ c`. -/
theorem H_shift2 (t c x : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ (2 * t) ∣ H p (c + x) - H p c - H p x + (c : ℤ_[p]) * S p 2 x := by
  rw [H_add, H_eq_sum p x, S2_eq_sum p x, add_sub_cancel_left, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.dvd_sum; intro j _
  exact inv_shift2 p t c (j + 1) hc

/- ### Lemma 2.1 (power sums over full blocks, general `d`) -/

/-- Multiplying the residues mod `p^v` by `a` (`p ∤ a`) permutes them:
`(a^d - 1) Σ′_{k < p^v} k^{-d} ≡ 0 (mod p^v)`. -/
lemma powsum_mul_cong (v d a : ℕ) (ha : ¬ p ∣ a) :
    (p : ℤ_[p]) ^ v ∣ ((a : ℤ_[p]) ^ d - 1) * ∑ k ∈ range (p ^ v), Ring.inverse (k : ℤ_[p]) ^ d := by
  haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  set n := p ^ v with hn
  set g : ZMod n → ℤ_[p] := fun x => Ring.inverse ((x.val : ℕ) : ℤ_[p]) ^ d with hg
  have hA : ∑ k ∈ range n, Ring.inverse (k : ℤ_[p]) ^ d = ∑ x : ZMod n, g x := by
    apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod n)) (fun x : ZMod n => x.val)
    · intro k _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro k hk; simp only [hg]; rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hk)]
  have hcop : Nat.Coprime a n :=
    (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha).symm).pow_right v
  set u := ZMod.unitOfCoprime a hcop with hu
  have hperm : ∑ x : ZMod n, g ((u : ZMod n) * x) = ∑ x : ZMod n, g x :=
    Equiv.sum_comp (Units.mulLeft u) g
  have hinv : (a : ℤ_[p]) * Ring.inverse (a : ℤ_[p]) = 1 := mul_inv_nat p ha
  have hterm : ∀ x : ZMod n, (p : ℤ_[p]) ^ v ∣ (a : ℤ_[p]) ^ d * g ((u : ZMod n) * x) - g x := by
    intro x
    have hval : ((u : ZMod n) * x).val = (a * x.val) % n := by
      rw [ZMod.val_mul, hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mul_mod a,
        Nat.mod_eq_of_lt (ZMod.val_lt x)]
    simp only [hg]
    rw [hval]
    have h1 := inv_pow_shift p v (n * (a * x.val / n)) ((a * x.val) % n) d (dvd_mul_right _ _)
    rw [Nat.div_add_mod] at h1
    have hmul : Ring.inverse (((a * x.val : ℕ)) : ℤ_[p])
        = Ring.inverse ((x.val : ℕ) : ℤ_[p]) * Ring.inverse (a : ℤ_[p]) := by
      rw [Nat.cast_mul, Ring.mul_inverse_rev]
    have e : (a : ℤ_[p]) ^ d * Ring.inverse (((a * x.val % n : ℕ)) : ℤ_[p]) ^ d
          - Ring.inverse ((x.val : ℕ) : ℤ_[p]) ^ d
        = -((a : ℤ_[p]) ^ d * (Ring.inverse (((a * x.val : ℕ)) : ℤ_[p]) ^ d
          - Ring.inverse (((a * x.val % n : ℕ)) : ℤ_[p]) ^ d)) := by
      rw [hmul, mul_pow]
      have h2 : (a : ℤ_[p]) ^ d * Ring.inverse (a : ℤ_[p]) ^ d = 1 := by
        rw [← mul_pow, hinv, one_pow]
      linear_combination (Ring.inverse ((x.val : ℕ) : ℤ_[p]) ^ d) * h2
    rw [e]
    exact (h1.mul_left _).neg_right
  have hsum := Finset.dvd_sum (fun x (_ : x ∈ (Finset.univ : Finset (ZMod n))) => hterm x)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hperm] at hsum
  rw [hA]
  have e : ((a : ℤ_[p]) ^ d - 1) * ∑ x : ZMod n, g x
      = (a : ℤ_[p]) ^ d * ∑ x : ZMod n, g x - ∑ x : ZMod n, g x := by ring
  rw [e]; exact hsum

/-- If `(p-1) ∤ d` there is `a` with `p ∤ a` and `a^d ≢ 1 (mod p)`. -/
lemma exists_pow_ne_one (d : ℕ) (hnd : ¬ (p - 1) ∣ d) : ∃ a : ℕ, ¬ p ∣ a ∧ ¬ p ∣ a ^ d - 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ x : (ZMod p)ˣ, ((x : ZMod p)) ^ d = 1 := by
    intro x
    have hx0 : (x : ZMod p) ≠ 0 := x.ne_zero
    have ha : ¬ p ∣ (x : ZMod p).val := by
      intro h
      apply hx0
      rw [← ZMod.natCast_zmod_val (x : ZMod p)]
      exact (ZMod.natCast_eq_zero_iff _ p).mpr h
    have h := hcon _ ha
    have ha1 : 1 ≤ (x : ZMod p).val ^ d :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h0 => ha (h0 ▸ dvd_zero p)))
    have h3 : (((x : ZMod p).val ^ d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
    rw [Nat.cast_sub ha1, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h3
    exact h3
  have hsum := FiniteField.sum_pow_units (ZMod p) d
  rw [ZMod.card p, if_neg hnd] at hsum
  simp only [hall, Finset.sum_const, Finset.card_univ, ZMod.card_units p, nsmul_eq_mul,
    mul_one] at hsum
  have h4 : p ∣ p - 1 := (ZMod.natCast_eq_zero_iff _ p).mp hsum
  have hp1 := (Fact.out : p.Prime).one_lt
  have := Nat.le_of_dvd (by omega) h4
  omega

lemma powsum_range (hp2 : p ≠ 2) (v d : ℕ) (hd : 1 ≤ d) :
    (p : ℤ_[p]) ^ (v - eD p d) ∣ ∑ k ∈ range (p ^ v), Ring.inverse (k : ℤ_[p]) ^ d := by
  have hp : p.Prime := Fact.out
  set A := ∑ k ∈ range (p ^ v), Ring.inverse (k : ℤ_[p]) ^ d with hA
  by_cases hnd : (p - 1) ∣ d
  · have heD : eD p d = 1 + padicValNat p d := by unfold eD; rw [if_pos hnd]
    rw [heD]
    have hnp : ¬ p ∣ 1 + p := by
      intro h; exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_refl p)).mp h)
    have h := powsum_mul_cong p v d (1 + p) hnp
    set N := (1 + p) ^ d - 1 with hN
    have hN1 : 1 ≤ (1 + p) ^ d := Nat.one_le_pow _ _ (by omega)
    have hcast : (((1 + p : ℕ)) : ℤ_[p]) ^ d - 1 = (N : ℤ_[p]) := by
      rw [hN, Nat.cast_sub hN1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at h
    have hN0 : N ≠ 0 := by
      have : 1 + 1 ≤ (1 + p) ^ d := by
        calc 1 + 1 ≤ 1 + p := by have := hp.two_le; omega
          _ = (1 + p) ^ 1 := (pow_one _).symm
          _ ≤ (1 + p) ^ d := Nat.pow_le_pow_right (by omega) hd
      omega
    have hp2' := hp.two_le
    have hval : padicValNat p N = 1 + padicValNat p d := by
      have := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2) (x := 1 + p) (y := 1)
        (by omega) (by simp) hnp (n := d) (by omega)
      rw [one_pow, show 1 + p - 1 = p by omega, padicValNat_self] at this
      exact this
    have hnd' := pow_succ_padicValNat_not_dvd (p := p) hN0
    obtain ⟨w, hw⟩ := pow_padicValNat_dvd (p := p) (n := N)
    set e := padicValNat p N with he
    have hpw : ¬ p ∣ w := by
      intro hpw
      apply hnd'
      rw [hw, pow_succ]; exact mul_dvd_mul_left _ hpw
    rw [hw, hval] at h
    have hwu := Epoch361883.isUnit_nat_of_not_dvd p hpw
    have h' : (p : ℤ_[p]) ^ v ∣ (p : ℤ_[p]) ^ (1 + padicValNat p d) * A := by
      have e : ((p ^ (1 + padicValNat p d) * w : ℕ) : ℤ_[p]) * A
          = (w : ℤ_[p]) * ((p : ℤ_[p]) ^ (1 + padicValNat p d) * A) := by push_cast; ring
      rw [e] at h
      exact (IsUnit.dvd_mul_left hwu).mp h
    rcases Nat.le_total v (1 + padicValNat p d) with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle, pow_zero]; exact one_dvd _
    · have hpe : (p : ℤ_[p]) ^ (1 + padicValNat p d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      rw [show v = (1 + padicValNat p d) + (v - (1 + padicValNat p d)) by omega, pow_add] at h'
      exact (mul_dvd_mul_iff_left hpe).mp h'
  · have heD : eD p d = 0 := by unfold eD; rw [if_neg hnd]
    rw [heD, Nat.sub_zero]
    obtain ⟨a, ha, had⟩ := exists_pow_ne_one p d hnd
    have h := powsum_mul_cong p v d a ha
    have ha1 : 1 ≤ a ^ d := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h0 => ha (h0 ▸ dvd_zero p)))
    have hcast : (a : ℤ_[p]) ^ d - 1 = ((a ^ d - 1 : ℕ) : ℤ_[p]) := by
      rw [Nat.cast_sub ha1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at h
    exact (IsUnit.dvd_mul_left (Epoch361883.isUnit_nat_of_not_dvd p had)).mp h

/-- **Lemma 2.1** (block form): `Σ′_{k ∈ B_v(l)} k^{-d} ≡ 0 (mod p^(v - e(d)))`. -/
theorem powsum_blk (hp2 : p ≠ 2) (v d l : ℕ) (hd : 1 ≤ d) :
    (p : ℤ_[p]) ^ (v - eD p d) ∣ ∑ k ∈ blk p v l, Ring.inverse (k : ℤ_[p]) ^ d := by
  have h := powsum_range p hp2 v d hd
  have hdiff : (p : ℤ_[p]) ^ (v - eD p d) ∣ ∑ k ∈ blk p v l, Ring.inverse (k : ℤ_[p]) ^ d
      - ∑ k ∈ range (p ^ v), Ring.inverse (k : ℤ_[p]) ^ d := by
    rw [sum_blk, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum; intro κ _
    exact (pow_dvd_pow _ (Nat.sub_le _ _)).trans
      (inv_pow_shift p v (l * p ^ v) κ d (dvd_mul_left _ _))
  have := dvd_add hdiff h
  rwa [sub_add_cancel] at this

/-- Lemma 2.1: `S_d(p^v y) ≡ 0 (mod p^(v - e(d)))`. -/
theorem S_dvd (hp2 : p ≠ 2) (v d y : ℕ) (hd : 1 ≤ d) :
    (p : ℤ_[p]) ^ (v - eD p d) ∣ S p d (p ^ v * y) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  have hpx : p ∣ p ^ v * y := (dvd_pow_self p (by omega)).mul_right y
  unfold S
  rw [Finset.sum_range_succ, inv_pow_eq_zero_of_dvd p hpx hd, add_zero, mul_comm, sum_range_blk]
  exact Finset.dvd_sum (fun l _ => powsum_blk p hp2 v d l hd)

omit [Fact p.Prime] in
lemma eD_two (hp5 : 5 ≤ p) : eD p 2 = 0 := by
  unfold eD
  rw [if_neg]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  omega

/- ### Lemma 2.5 (double harmonic sums, first kind) -/

/-- `σ_s(c + n) ≡ σ_s(n) (mod p^(t+2s))` when `p^t ∣ c`. -/
lemma sig_shift (hp5 : 5 ≤ p) (s t c n : ℕ) (hc : p ^ t ∣ c) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ sig p s (c + n) - sig p s n := by
  unfold sig
  rw [sum_blk, sum_blk]
  have hC : p ^ (t + s) ∣ c * p ^ s := by rw [pow_add]; exact mul_dvd_mul_right hc _
  have e : ∀ κ, (c + n) * p ^ s + κ = c * p ^ s + (n * p ^ s + κ) := fun κ => by ring
  simp_rw [e]
  set C := ((c * p ^ s : ℕ) : ℤ_[p]) with hCdef
  have hsplit : ∑ κ ∈ range (p ^ s), Ring.inverse (((c * p ^ s + (n * p ^ s + κ) : ℕ)) : ℤ_[p])
      - ∑ κ ∈ range (p ^ s), Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p])
      = ∑ κ ∈ range (p ^ s), (Ring.inverse (((c * p ^ s + (n * p ^ s + κ) : ℕ)) : ℤ_[p])
          - Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p])
          + C * Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p]) ^ 2)
        - C * ∑ κ ∈ range (p ^ s), Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p]) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]; ring
  rw [hsplit]
  apply _root_.dvd_sub
  · apply Finset.dvd_sum; intro κ _
    exact (pow_dvd_pow _ (by omega)).trans (inv_shift2 p (t + s) (c * p ^ s) (n * p ^ s + κ) hC)
  · have hb := invsq_blk p hp5 s n
    rw [sum_blk] at hb
    rw [show t + 2 * s = (t + s) + s by ring, pow_add]
    exact mul_dvd_mul (ppow_dvd_natCast p hC) hb

lemma shift_one_sum (B s : ℕ) (hs : 1 ≤ s) (hB : p ∣ B) :
    ∑ κ ∈ range (p ^ s), Ring.inverse (((B + (κ + 1) : ℕ)) : ℤ_[p])
      = ∑ κ ∈ range (p ^ s), Ring.inverse (((B + κ : ℕ)) : ℤ_[p]) := by
  have h1 := Finset.sum_range_succ (fun κ => Ring.inverse (((B + κ : ℕ)) : ℤ_[p])) (p ^ s)
  have h2 := Finset.sum_range_succ' (fun κ => Ring.inverse (((B + κ : ℕ)) : ℤ_[p])) (p ^ s)
  have hz1 : Ring.inverse (((B + p ^ s : ℕ)) : ℤ_[p]) = 0 :=
    inv_eq_zero_of_dvd p (dvd_add hB (dvd_pow_self p (by omega)))
  have hz0 : Ring.inverse (((B + 0 : ℕ)) : ℤ_[p]) = 0 := inv_eq_zero_of_dvd p (by simpa using hB)
  beta_reduce at h1 h2
  linear_combination h1 - h2 + hz1 - hz0

omit [Fact p.Prime] in
lemma arith_refl (B Y P Q κ : ℕ) (h : B + Y + P = Q) (hκ : κ < P) :
    B + (P - 1 - κ + 1) = Q - (Y + κ) := by omega

/-- `σ_s(p^t - 1 - n) = Σ′_{k ∈ B_s(n)} 1/(p^(t+s) - k)` (`s ≥ 1`). -/
lemma sig_refl_eq (s t n : ℕ) (hs : 1 ≤ s) (hn : n < p ^ t) :
    sig p s (p ^ t - 1 - n) = ∑ κ ∈ range (p ^ s),
      Ring.inverse (((p ^ t * p ^ s - (n * p ^ s + κ) : ℕ)) : ℤ_[p]) := by
  have hps : p ∣ p ^ s := dvd_pow_self p (by omega)
  unfold sig
  rw [sum_blk, ← shift_one_sum p _ s hs (hps.mul_left _), ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl; intro κ hκ
  simp only [Finset.mem_range] at hκ
  have hB : (p ^ t - 1 - n) * p ^ s + n * p ^ s + p ^ s = p ^ t * p ^ s := by
    have e : (p ^ t - 1 - n) * p ^ s + n * p ^ s + p ^ s = (p ^ t - 1 - n + n + 1) * p ^ s := by ring
    rw [e, show p ^ t - 1 - n + n + 1 = p ^ t by omega]
  rw [arith_refl _ _ _ _ _ hB hκ]

/-- `σ_s(n) + σ_s(p^t - 1 - n) ≡ 0 (mod p^(t+2s))` for `s ≥ 1`, `n < p^t`. -/
lemma sig_refl (hp5 : 5 ≤ p) (s t n : ℕ) (hs : 1 ≤ s) (hn : n < p ^ t) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ sig p s n + sig p s (p ^ t - 1 - n) := by
  have hNd : p ^ (t + s) ∣ p ^ t * p ^ s := by rw [pow_add]
  have hpN : p ∣ p ^ t * p ^ s := (dvd_pow_self p (by omega)).mul_left _
  rw [sig_refl_eq p s t n hs hn]
  unfold sig; rw [sum_blk, ← Finset.sum_add_distrib]
  set N := ((p ^ t * p ^ s : ℕ) : ℤ_[p]) with hN
  have hterm : ∀ κ ∈ range (p ^ s), Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p])
        + Ring.inverse (((p ^ t * p ^ s - (n * p ^ s + κ) : ℕ)) : ℤ_[p])
      = -N * Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p]) ^ 2
        + N ^ 2 * (Ring.inverse (((n * p ^ s + κ : ℕ)) : ℤ_[p]) ^ 2
          * Ring.inverse (((p ^ t * p ^ s - (n * p ^ s + κ) : ℕ)) : ℤ_[p])) := by
    intro κ hκ
    simp only [Finset.mem_range] at hκ
    have hle : n * p ^ s + κ ≤ p ^ t * p ^ s := by
      have : (n + 1) * p ^ s ≤ p ^ t * p ^ s := Nat.mul_le_mul_right _ hn
      rw [add_mul, one_mul] at this; omega
    have h := inv_sub_expand p (p ^ t * p ^ s) (n * p ^ s + κ) hpN hle
    linear_combination h
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  apply dvd_add
  · have hb := invsq_blk p hp5 s n
    rw [sum_blk] at hb
    rw [show t + 2 * s = (t + s) + s by ring, pow_add]
    exact mul_dvd_mul (ppow_dvd_natCast p hNd).neg_right hb
  · have h2 := pow_dvd_pow_of_dvd (ppow_dvd_natCast p hNd) 2
    rw [← pow_mul] at h2
    exact ((pow_dvd_pow _ (by omega)).trans h2).mul_right _

/-- Base block of Lemma 2.5, `s ≥ 1`. -/
lemma dh1_base_pos (hp5 : 5 ≤ p) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ ∑ n ∈ range (p ^ t), sig p s n * H p n := by
  have hrefl : ∑ n ∈ range (p ^ t), sig p s n * H p n
      = ∑ n ∈ range (p ^ t), sig p s (p ^ t - 1 - n) * H p (p ^ t - 1 - n) :=
    (Finset.sum_range_reflect (fun n => sig p s n * H p n) (p ^ t)).symm
  have h2 : 2 * ∑ n ∈ range (p ^ t), sig p s n * H p n
      = ∑ n ∈ range (p ^ t), ((sig p s n + sig p s (p ^ t - 1 - n)) * H p n
        + sig p s (p ^ t - 1 - n) * (H p (p ^ t - 1 - n) - H p n)) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _; ring
  apply dvd_of_two_mul p hp5
  rw [h2]
  apply Finset.dvd_sum; intro n hn
  simp only [Finset.mem_range] at hn
  apply dvd_add
  · exact (sig_refl p hp5 s t n hs hn).mul_right _
  · rw [add_comm, pow_add]
    exact mul_dvd_mul (sig_dvd p hp5 s _) (refl_weak p hp5 t n ht hn)

/-- Base block of Lemma 2.5, `s = 0`. -/
lemma dh1_base_zero (hp5 : 5 ≤ p) (t : ℕ) (ht : 1 ≤ t) :
    (p : ℤ_[p]) ^ t ∣ ∑ n ∈ range (p ^ t), Ring.inverse (n : ℤ_[p]) * H p n := by
  set N := p ^ t with hN
  have hpN : p ∣ N := dvd_pow_self p (by omega)
  have hext : ∑ n ∈ range N, Ring.inverse (n : ℤ_[p]) * H p n
      = ∑ n ∈ range (N + 1), Ring.inverse (n : ℤ_[p]) * H p n := by
    rw [Finset.sum_range_succ, inv_eq_zero_of_dvd p hpN, zero_mul, add_zero]
  have hrefl : ∑ n ∈ range (N + 1), Ring.inverse (n : ℤ_[p]) * H p n
      = ∑ n ∈ range (N + 1), Ring.inverse ((N - n : ℕ) : ℤ_[p]) * H p (N - n) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro n _
    rw [show N + 1 - 1 - n = N - n by omega]
  have hsq : ∑ n ∈ range (N + 1), Ring.inverse ((N - n : ℕ) : ℤ_[p]) ^ 2 = S p 2 N := by
    unfold S
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro n hn
    simp only [Finset.mem_range] at hn
    rw [show N + 1 - 1 - n = N - n by omega, show N - (N - n) = n by omega]
  have hsplit : ∀ n ∈ range (N + 1), Ring.inverse ((N - n : ℕ) : ℤ_[p]) * H p (N - n)
      = Ring.inverse ((N - n : ℕ) : ℤ_[p]) * H p (N - 1 - n)
        + Ring.inverse ((N - n : ℕ) : ℤ_[p]) ^ 2 := by
    intro n hn
    simp only [Finset.mem_range] at hn
    by_cases h : n = N
    · subst h; simp
    · rw [show N - n = (N - 1 - n) + 1 by omega, H_succ]; ring
  have h2 : 2 * ∑ n ∈ range N, Ring.inverse (n : ℤ_[p]) * H p n
      = ∑ n ∈ range (N + 1), ((Ring.inverse (n : ℤ_[p]) + Ring.inverse ((N - n : ℕ) : ℤ_[p])) * H p n
          + Ring.inverse ((N - n : ℕ) : ℤ_[p]) * (H p (N - 1 - n) - H p n))
        + S p 2 N := by
    rw [two_mul, hext]
    nth_rewrite 2 [hrefl]
    rw [Finset.sum_congr rfl hsplit, ← hsq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _; ring
  apply dvd_of_two_mul p hp5
  rw [h2]
  refine dvd_add (Finset.dvd_sum fun n hn => ?_) (S2_dvd' p hp5 t N dvd_rfl)
  simp only [Finset.mem_range] at hn
  apply dvd_add
  · rw [inv_add_inv_sub p N n hpN (by omega)]
    exact ((ppow_dvd_natCast p dvd_rfl).mul_right _).mul_right _
  · by_cases h : n = N
    · subst h; simp
    · exact (refl_weak p hp5 t n ht (by omega)).mul_left _

/-- **Lemma 2.5**: `Σ_{n ∈ B_t(i)} σ_s(n) H′_n ≡ 0 (mod p^(t+2s))`. -/
theorem dh1 (hp5 : 5 ≤ p) (s t i : ℕ) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ ∑ n ∈ blk p t i, sig p s n * H p n := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [blk_zero, Finset.sum_singleton, zero_add]; exact (sig_dvd p hp5 s i).mul_right _
  have hbase : (p : ℤ_[p]) ^ (t + 2 * s) ∣ ∑ n ∈ range (p ^ t), sig p s n * H p n := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [sig_zero, Nat.mul_zero, add_zero]; exact dh1_base_zero p hp5 t ht
    · exact dh1_base_pos p hp5 s t hs ht
  have hc : p ^ t ∣ i * p ^ t := dvd_mul_left _ _
  rw [sum_blk]
  have e : ∀ n ∈ range (p ^ t), sig p s (i * p ^ t + n) * H p (i * p ^ t + n)
      = (sig p s (i * p ^ t + n) * (H p (i * p ^ t + n) - H p (i * p ^ t) - H p n)
          + (sig p s (i * p ^ t + n) - sig p s n) * H p n)
        + H p (i * p ^ t) * sig p s (i * p ^ t + n) + sig p s n * H p n := by
    intro n _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine dvd_add (dvd_add (Finset.dvd_sum fun n _ => ?_) ?_) hbase
  · apply dvd_add
    · rw [add_comm, pow_add]
      exact mul_dvd_mul (sig_dvd p hp5 s _) (H_shift p t _ n hc)
    · exact (sig_shift p hp5 s t _ n hc).mul_right _
  · have hm : ∑ n ∈ range (p ^ t), sig p s (i * p ^ t + n) = sig p (s + t) i := by
      rw [← sum_blk, sig_merge]
    rw [hm]
    have h1 := mul_dvd_mul (H_dvd p hp5 t _ hc) (sig_dvd p hp5 (s + t) i)
    rw [← pow_add] at h1
    exact (pow_dvd_pow _ (by omega)).trans h1

/- ### Lemma 2.6 (double harmonic sums, second kind) -/

lemma dh2_base (hp5 : 5 ≤ p) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ ∑ k ∈ range (p ^ t), Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s) := by
  set N := p ^ t with hN
  have hpN : p ∣ N := dvd_pow_self p (by omega)
  have hext : ∑ k ∈ range N, Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s)
      = ∑ k ∈ range (N + 1), Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s) := by
    rw [Finset.sum_range_succ, inv_eq_zero_of_dvd p hpN, zero_mul, add_zero]
  have hrefl : ∑ k ∈ range (N + 1), Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s)
      = ∑ k ∈ range (N + 1), Ring.inverse ((N - k : ℕ) : ℤ_[p]) * H p ((N - k) * p ^ s) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro k _
    rw [show N + 1 - 1 - k = N - k by omega]
  have h2 : 2 * ∑ k ∈ range N, Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s)
      = ∑ k ∈ range (N + 1), ((Ring.inverse (k : ℤ_[p]) + Ring.inverse ((N - k : ℕ) : ℤ_[p]))
          * H p (k * p ^ s)
        + Ring.inverse ((N - k : ℕ) : ℤ_[p]) * (H p ((N - k) * p ^ s) - H p (k * p ^ s))) := by
    rw [two_mul, hext]
    nth_rewrite 2 [hrefl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  apply dvd_of_two_mul p hp5
  rw [h2]
  apply Finset.dvd_sum; intro k hk
  simp only [Finset.mem_range] at hk
  apply dvd_add
  · rw [inv_add_inv_sub p N k hpN (by omega), pow_add]
    exact mul_dvd_mul ((ppow_dvd_natCast p dvd_rfl).mul_right _)
      (H_dvd p hp5 s _ (dvd_mul_left _ _))
  · exact (refl_scaled p hp5 s t k hs ht (by omega)).mul_left _

/-- **Lemma 2.6**: `Σ′_{k ∈ B_t(i)} (1/k) H′_{k p^s} ≡ 0 (mod p^(t+2s))`. -/
theorem dh2 (hp5 : 5 ≤ p) (s t i : ℕ) :
    (p : ℤ_[p]) ^ (t + 2 * s) ∣ ∑ k ∈ blk p t i, Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have h := dh1 p hp5 0 t i
    simp only [sig_zero] at h
    simpa using h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [blk_zero, Finset.sum_singleton, zero_add]
    exact (H_dvd p hp5 s _ (dvd_mul_left _ _)).mul_left _
  have hbase := dh2_base p hp5 s t hs ht
  have hc : p ^ t ∣ i * p ^ t := dvd_mul_left _ _
  rw [sum_blk]
  have e : ∑ k ∈ range (p ^ t), Ring.inverse (((i * p ^ t + k : ℕ)) : ℤ_[p]) * H p ((i * p ^ t + k) * p ^ s)
      = ∑ k ∈ range (p ^ t), (Ring.inverse (((i * p ^ t + k : ℕ)) : ℤ_[p]) * H p ((i * p ^ t + k) * p ^ s)
          - Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s))
        + ∑ k ∈ range (p ^ t), Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  rw [e]
  refine dvd_add (Finset.dvd_sum fun k _ => ?_) hbase
  have hC : p ^ (t + s) ∣ i * p ^ t * p ^ s := by rw [pow_add]; exact mul_dvd_mul_right hc _
  have hsplit : Ring.inverse (((i * p ^ t + k : ℕ)) : ℤ_[p]) * H p ((i * p ^ t + k) * p ^ s)
        - Ring.inverse (k : ℤ_[p]) * H p (k * p ^ s)
      = (Ring.inverse (((i * p ^ t + k : ℕ)) : ℤ_[p]) - Ring.inverse (k : ℤ_[p]))
          * H p ((i * p ^ t + k) * p ^ s)
        + Ring.inverse (k : ℤ_[p]) * ((H p (i * p ^ t * p ^ s + k * p ^ s) - H p (i * p ^ t * p ^ s)
            - H p (k * p ^ s) + ((i * p ^ t * p ^ s : ℕ) : ℤ_[p]) * S p 2 (k * p ^ s))
          + H p (i * p ^ t * p ^ s) - ((i * p ^ t * p ^ s : ℕ) : ℤ_[p]) * S p 2 (k * p ^ s)) := by
    rw [show (i * p ^ t + k) * p ^ s = i * p ^ t * p ^ s + k * p ^ s by ring]; ring
  rw [hsplit]
  apply dvd_add
  · rw [pow_add]
    exact mul_dvd_mul (inv_shift p t _ k hc) (H_dvd p hp5 s _ (dvd_mul_left _ _))
  · apply Dvd.dvd.mul_left
    refine _root_.dvd_sub (dvd_add ?_ ?_) ?_
    · exact (pow_dvd_pow _ (by omega)).trans (H_shift2 p (t + s) _ _ hC)
    · exact (pow_dvd_pow _ (by omega)).trans (H_dvd p hp5 (t + s) _ hC)
    · rw [show t + 2 * s = (t + s) + s by ring, pow_add]
      exact mul_dvd_mul (ppow_dvd_natCast p hC) (S2_dvd' p hp5 s _ (dvd_mul_left _ _))

/- ### Lemma 2.7 (carry-restricted sums) -/

omit [Fact p.Prime] in
lemma cry_le_one (t a b δ : ℕ) : cry p t a b δ ≤ 1 := by
  unfold cry; split_ifs <;> omega

/-- The inner carry sum: for `n = i p^t + n̄`, `Σ_{j ∈ B_t(i'), carry} 1/j ≡ -(H′_n - H′_{i p^t})`. -/
lemma carry_inner (hp5 : 5 ≤ p) (t i i' nb : ℕ) (ht : 1 ≤ t) (hnb : nb < p ^ t) :
    (p : ℤ_[p]) ^ t ∣ (∑ j ∈ blk p t i', if cry p t (i * p ^ t + nb) j 0 = 1
        then Ring.inverse (j : ℤ_[p]) else 0)
      + H p (i * p ^ t + nb) - H p (i * p ^ t) := by
  have hpt : p ∣ p ^ t := dvd_pow_self p (by omega)
  have hc' : p ^ t ∣ i' * p ^ t := dvd_mul_left _ _
  rw [sum_blk]
  have hcond : ∀ j ∈ range (p ^ t), (cry p t (i * p ^ t + nb) (i' * p ^ t + j) 0 = 1 ↔ p ^ t ≤ nb + j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    unfold cry
    rw [Nat.add_comm (i * p ^ t), Nat.add_mul_mod_self_right, Nat.add_comm (i' * p ^ t),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hj, add_zero]
    split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl (fun j hj => by rw [if_congr (hcond j hj) rfl rfl]), ← Finset.sum_filter]
  have hfil : (range (p ^ t)).filter (fun j => p ^ t ≤ nb + j) = Ico (p ^ t - nb) (p ^ t) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil]
  have hJ'' : ∑ j ∈ Ico (p ^ t - nb) (p ^ t), Ring.inverse (j : ℤ_[p])
      = H p (p ^ t) - H p (p ^ t - 1 - nb) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), sum_range_inv_eq_H p hpt,
      sum_range_inv_eq_H_pred p (by omega : 1 ≤ p ^ t - nb), show p ^ t - nb - 1 = p ^ t - 1 - nb by omega]
  have e : ∑ j ∈ Ico (p ^ t - nb) (p ^ t), Ring.inverse (((i' * p ^ t + j : ℕ)) : ℤ_[p])
        + H p (i * p ^ t + nb) - H p (i * p ^ t)
      = ∑ j ∈ Ico (p ^ t - nb) (p ^ t), (Ring.inverse (((i' * p ^ t + j : ℕ)) : ℤ_[p])
          - Ring.inverse (j : ℤ_[p]))
        + H p (p ^ t) - (H p (p ^ t - 1 - nb) - H p nb)
        + (H p (i * p ^ t + nb) - H p (i * p ^ t) - H p nb) := by
    rw [Finset.sum_sub_distrib, hJ'']; ring
  rw [e]
  refine dvd_add (_root_.dvd_sub (dvd_add (Finset.dvd_sum fun j _ => inv_shift p t _ j hc') ?_) ?_) ?_
  · exact (pow_dvd_pow _ (by omega)).trans (H_dvd p hp5 t _ dvd_rfl)
  · exact refl_weak p hp5 t nb ht hnb
  · exact H_shift p t _ nb (dvd_mul_left _ _)

/-- **Lemma 2.7 (Y)** (also `t = 0`): the sum of `σ_{s'}(n)/j` over the cell
`{n ∈ B_t(i), j ∈ B_t(i'), p ∤ j, carry = c}` is `≡ 0 (mod p^(t+2s'))`. -/
theorem carry_Y (hp5 : 5 ≤ p) (s' t i i' c : ℕ) :
    (p : ℤ_[p]) ^ (t + 2 * s') ∣ ∑ n ∈ blk p t i, ∑ j ∈ blk p t i',
      if cry p t n j 0 = c then sig p s' n * Ring.inverse (j : ℤ_[p]) else 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [blk_zero, blk_zero, Finset.sum_singleton, Finset.sum_singleton, zero_add]
    have hcry : cry p 0 i i' 0 = 0 := by unfold cry; simp [Nat.mod_one]
    rw [hcry]
    split_ifs
    · exact (sig_dvd p hp5 s' i).mul_right _
    · exact dvd_zero _
  set Cc : ℕ → ℤ_[p] := fun c => ∑ n ∈ blk p t i, ∑ j ∈ blk p t i',
      if cry p t n j 0 = c then sig p s' n * Ring.inverse (j : ℤ_[p]) else 0 with hCc
  show (p : ℤ_[p]) ^ (t + 2 * s') ∣ Cc c
  -- the carry-one cell
  have h1 : (p : ℤ_[p]) ^ (t + 2 * s') ∣ Cc 1 := by
    have e1 : Cc 1 = ∑ n ∈ blk p t i, sig p s' n * (∑ j ∈ blk p t i',
        if cry p t n j 0 = 1 then Ring.inverse (j : ℤ_[p]) else 0) := by
      simp only [hCc]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      split_ifs <;> ring
    have e2 : ∑ n ∈ blk p t i, sig p s' n * (∑ j ∈ blk p t i',
        if cry p t n j 0 = 1 then Ring.inverse (j : ℤ_[p]) else 0)
        = ∑ n ∈ blk p t i, sig p s' n * ((∑ j ∈ blk p t i',
            if cry p t n j 0 = 1 then Ring.inverse (j : ℤ_[p]) else 0) + H p n - H p (i * p ^ t))
          - ∑ n ∈ blk p t i, sig p s' n * H p n
          + H p (i * p ^ t) * ∑ n ∈ blk p t i, sig p s' n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [e1, e2]
    refine dvd_add (_root_.dvd_sub ?_ (dh1 p hp5 s' t i)) ?_
    · rw [sum_blk]
      apply Finset.dvd_sum; intro nb hnb
      simp only [Finset.mem_range] at hnb
      rw [add_comm, pow_add]
      exact mul_dvd_mul (sig_dvd p hp5 s' _) (carry_inner p hp5 t i i' nb ht hnb)
    · rw [sig_merge]
      have h := mul_dvd_mul (H_dvd p hp5 t (i * p ^ t) (dvd_mul_left _ _)) (sig_dvd p hp5 (s' + t) i)
      rw [← pow_add] at h
      exact (pow_dvd_pow _ (by omega)).trans h
  -- the full sum
  have htot : (p : ℤ_[p]) ^ (t + 2 * s') ∣ Cc 0 + Cc 1 := by
    have e : Cc 0 + Cc 1 = (∑ n ∈ blk p t i, sig p s' n) * sig p t i' := by
      simp only [hCc]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      unfold sig
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (cry_le_one p t n j 0) with h | h <;> simp [h]
    rw [e, sig_merge]
    exact (pow_dvd_pow _ (by omega)).trans ((sig_dvd p hp5 (s' + t) i).mul_right _)
  rcases Nat.lt_or_ge c 2 with hc | hc
  · interval_cases c
    · have := _root_.dvd_sub htot h1; rwa [add_sub_cancel_right] at this
    · exact h1
  · have h0 : Cc c = 0 := by
      simp only [hCc]
      apply Finset.sum_eq_zero; intro n _; apply Finset.sum_eq_zero; intro j _
      have := cry_le_one p t n j 0
      rw [if_neg (by omega)]
    rw [h0]; exact dvd_zero _

/-- **Lemma 2.7 (B)**: the sum of `1/(kj)` over the cell (`p ∤ k`, `p ∤ j`) is `≡ 0 (mod p^t)`. -/
theorem carry_B (hp5 : 5 ≤ p) (t i i' c : ℕ) :
    (p : ℤ_[p]) ^ t ∣ ∑ k ∈ blk p t i, ∑ j ∈ blk p t i',
      if cry p t k j 0 = c then Ring.inverse (k : ℤ_[p]) * Ring.inverse (j : ℤ_[p]) else 0 := by
  have h := carry_Y p hp5 0 t i i' c
  simp only [sig_zero, Nat.mul_zero, add_zero] at h
  exact h

end harm

end ShiftLib
