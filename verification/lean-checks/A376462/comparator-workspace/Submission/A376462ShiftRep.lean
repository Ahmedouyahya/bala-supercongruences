import Submission.A376462Defs
import Submission.ShiftLibBlock

/-!
# A376462 shifted congruence, part 1: representation, class split, helpers

Proof note: `proofs/A376462-shifted-congruence.md`, §0.

* `rep_shift`: `A376462 (N - 1) = Σ_{k<N} Σ_{j<N} S̃(N;k,j)` (reflection `i ↦ (n-k) - i` in
  `a108625_aux`), with `S̃ = ShiftLib.St`.
* `split4`: `a(N-1) - a(M-1) = (Σ_S - a(M-1)) + Σ_J + Σ_K + Σ_B` in `ℤ_[p]`
  (`N = m p^(w+1)`, `M = m p^w`), classes by divisibility of `k`, `j` by `p`.
* helpers: `split_tower`, `sum_filter_ndvd`, the factorisations of `S̃` for the classes.
-/

open Nat Finset

namespace A376462Shift

open ShiftLib

/-- Reflection: `A108625(n, n-k) = Σ_{j ≤ n} C(n,k+j)² C(n+j,j)` for `k ≤ n`. -/
lemma aux_refl (n k : ℕ) (hk : k ≤ n) :
    a108625_aux n (n - k) = ∑ j ∈ range (n + 1), n.choose (k + j) ^ 2 * (n + j).choose j := by
  unfold a108625_aux
  rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_range_add_sum_Ico _ (show n - k + 1 ≤ n + 1 by omega)]
  have h0 : ∑ j ∈ Ico (n - k + 1) (n + 1), n.choose (k + j) ^ 2 * (n + j).choose j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega : n < k + j)]
    ring
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show n - k + 1 - 1 - j = n - (k + j) by omega, Nat.choose_symm (by omega : k + j ≤ n),
    show n + (n - k) - (n - (k + j)) = n + j by omega, show n - k - (n - (k + j)) = j by omega]

/-- **Representation.** `a(N-1) = Σ_{k<N} Σ_{j<N} S̃(N;k,j)`. -/
theorem rep_shift (N : ℕ) (hN : 1 ≤ N) :
    A376462 (N - 1) = ∑ k ∈ range N, ∑ j ∈ range N, St N k j := by
  unfold A376462
  rw [show N - 1 + 1 = N by omega]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [aux_refl (N - 1) k (by omega), show N - 1 + 1 = N by omega, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold St
  rw [show N - 1 + k = N + k - 1 by omega, show N - 1 + j = N + j - 1 by omega]
  ring

section helpers

variable (p : ℕ) [Fact p.Prime]

lemma inv_mul_nat {k : ℕ} (h : ¬ p ∣ k) : Ring.inverse (k : ℤ_[p]) * (k : ℤ_[p]) = 1 := by
  rw [mul_comm]; exact mul_inv_nat p h

/-- Tower congruence for a sum split into scaled and unscaled indices. -/
lemma split_tower (M' u : ℕ) (f g : ℕ → ℤ_[p])
    (h1 : ∀ j, (p : ℤ_[p]) ^ u ∣ f (p * j) - g j)
    (h2 : ∀ j, ¬ p ∣ j → (p : ℤ_[p]) ^ u ∣ f j) :
    (p : ℤ_[p]) ^ u ∣ ∑ j ∈ range (p * M'), f j - ∑ j ∈ range M', g j := by
  rw [sum_range_mul_split p M' f]
  have e : ∑ j ∈ range M', f (p * j) + ∑ k ∈ (range (p * M')).filter (fun k => ¬ p ∣ k), f k
      - ∑ j ∈ range M', g j
      = ∑ j ∈ range M', (f (p * j) - g j)
        + ∑ k ∈ (range (p * M')).filter (fun k => ¬ p ∣ k), f k := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  exact dvd_add (Finset.dvd_sum fun j _ => h1 j)
    (Finset.dvd_sum fun k hk => h2 k (Finset.mem_filter.mp hk).2)

/-- Dropping the filter `p ∤ k` when the summand vanishes on multiples of `p`. -/
lemma sum_filter_ndvd (s : Finset ℕ) (f : ℕ → ℤ_[p]) (hf : ∀ k, p ∣ k → f k = 0) :
    ∑ k ∈ s.filter (fun k => ¬ p ∣ k), f k = ∑ k ∈ s, f k := by
  apply Finset.sum_filter_of_ne
  intro k _ hk h
  exact hk (hf k h)

omit [Fact p.Prime] in
lemma not_dvd_add {N k : ℕ} (hN : p ∣ N) (hk : ¬ p ∣ k) : ¬ p ∣ N + k :=
  fun h => hk ((Nat.dvd_add_right hN).mp h)

lemma inv_add_eq_zero {N k : ℕ} (hN : p ∣ N) (hk : p ∣ k) :
    Ring.inverse ((N + k : ℕ) : ℤ_[p]) = 0 :=
  inv_eq_zero_of_dvd p (dvd_add hN hk)

/-- `p^u ∣ C(m p^u + j - 1, j)` for `p ∤ j`. -/
lemma choose_unsc (m u j : ℕ) (hj : ¬ p ∣ j) :
    (p : ℤ_[p]) ^ u ∣ (((m * p ^ u + j - 1).choose j : ℕ) : ℤ_[p]) := by
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => hj (h ▸ dvd_zero p))
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (choose_absorb_pred (m * p ^ u) j hj1)
  push_cast at h
  have h2 : (p : ℤ_[p]) ^ u ∣ (j : ℤ_[p]) * (((m * p ^ u + j - 1).choose j : ℕ) : ℤ_[p]) := by
    rw [h]; exact ⟨(m : ℤ_[p]) * (((m * p ^ u + j - 1).choose (j - 1) : ℕ) : ℤ_[p]), by ring⟩
  exact (IsUnit.dvd_mul_left (Epoch361883.isUnit_nat_of_not_dvd p hj)).mp h2

/-- `C(L + x - 1, x) = L · x⁻¹ · C(L + x - 1, x - 1)` for `p ∤ x`. -/
lemma choose_unsc_eq (L x : ℕ) (hx : ¬ p ∣ x) :
    (((L + x - 1).choose x : ℕ) : ℤ_[p])
      = (L : ℤ_[p]) * Ring.inverse (x : ℤ_[p]) * (((L + x - 1).choose (x - 1) : ℕ) : ℤ_[p]) := by
  have hx1 : 1 ≤ x := Nat.pos_of_ne_zero (fun h => hx (h ▸ dvd_zero p))
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (choose_absorb_pred L x hx1)
  push_cast at h
  have hu := inv_mul_nat p hx
  linear_combination (-(((L + x - 1).choose x : ℕ) : ℤ_[p])) * hu + Ring.inverse (x : ℤ_[p]) * h

/-- Class K/B factorisation: `S̃(N;k,j) = N (N+k)⁻¹ Ψ(N;k,j)` for `p ∤ k`. -/
lemma St_eq_K (N k j : ℕ) (hN : 1 ≤ N) (hpN : p ∣ N) (hk : ¬ p ∣ k) :
    ((St N k j : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * Ring.inverse ((N + k : ℕ) : ℤ_[p]) * ((Psi N k j : ℕ) : ℤ_[p]) := by
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (St_factor N k j hN)
  have hu := inv_mul_nat p (not_dvd_add p hpN hk)
  push_cast at h hu ⊢
  linear_combination (-((St N k j : ℕ) : ℤ_[p])) * hu + Ring.inverse ((N : ℤ_[p]) + k) * h

/-- `Ψ_u(n,j) = L j⁻¹ Ξ̂_u(n,j)` for `p ∤ j`. -/
lemma Psi_eq_unsc (L n j : ℕ) (hj : ¬ p ∣ j) :
    ((Psi L n j : ℕ) : ℤ_[p])
      = (L : ℤ_[p]) * Ring.inverse (j : ℤ_[p]) * ((Xih L n j : ℕ) : ℤ_[p]) := by
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => hj (h ▸ dvd_zero p))
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (Psi_factor L n j hj1)
  have hu := inv_mul_nat p hj
  push_cast at h
  linear_combination (-((Psi L n j : ℕ) : ℤ_[p])) * hu + Ring.inverse (j : ℤ_[p]) * h

/-- **Class split.** -/
theorem split4 (m w : ℕ) (hm : 1 ≤ m) :
    ((A376462 (m * p ^ (w + 1) - 1) : ℕ) : ℤ_[p]) - ((A376462 (m * p ^ w - 1) : ℕ) : ℤ_[p])
      = (∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
            (((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p])
              - ((St (m * p ^ w) k j : ℕ) : ℤ_[p])))
        + ∑ k ∈ range (m * p ^ w), ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
            ((St (m * p ^ (w + 1)) (p * k) j : ℕ) : ℤ_[p])
        + ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k), ∑ j ∈ range (m * p ^ w),
            ((St (m * p ^ (w + 1)) k (p * j) : ℕ) : ℤ_[p])
        + ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
            ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
            ((St (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hM : 1 ≤ m * p ^ w :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hN : 1 ≤ m * p ^ (w + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hs : ∀ f : ℕ → ℤ_[p], ∑ k ∈ range (m * p ^ (w + 1)), f k
      = ∑ j ∈ range (m * p ^ w), f (p * j)
        + ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k), f k := by
    intro f
    rw [show m * p ^ (w + 1) = p * (m * p ^ w) by ring]
    exact sum_range_mul_split p _ f
  rw [rep_shift _ hN, rep_shift _ hM]
  push_cast
  simp only [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end helpers

end A376462Shift
