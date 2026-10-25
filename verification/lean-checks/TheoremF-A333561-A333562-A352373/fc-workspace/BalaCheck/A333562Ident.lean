import Mathlib
import FormalConjectures.OEIS.Auto.«333562_2eccaf4c»

/-!
A binomial identity for OEIS A333562:
`a n = Σ_{k=0}^{3n} C(4n, 3n-k) C(n+k-1, k)` for `n ≥ 1`, where
`a n = Σ_{j=0}^{3n} C(n+j-1, j) 2^j` (the definition in the imported target module).

Throughout, `n = m + 1`.
-/

open Finset

namespace A333562

/-- summand `f(K,i) = C(m+K, K-i) C(m+i, i)` -/
def f (m K i : ℕ) : ℕ := (m + K).choose (K - i) * (m + i).choose i

/-- `D(m+1, K) = Σ_{i=0}^{K} C(m+K, K-i) C(m+i, i)` -/
def D (m K : ℕ) : ℕ := ∑ i ∈ range (K + 1), f m K i

/-- certificate `G(K,i) = i C(m+K+1, K+1-i) C(m+i, i)` (in `ℤ`) -/
def G (m K i : ℕ) : ℤ := (i : ℤ) * ((m + K + 1).choose (K + 1 - i) : ℤ) * ((m + i).choose i : ℤ)

/-- `S(m+1, K) = Σ_{j=0}^{K} C(m+j, j) 2^j` -/
def S (m K : ℕ) : ℕ := ∑ j ∈ range (K + 1), (m + j).choose j * 2 ^ j

/-- `R(m+1, K) = Σ_{k=0}^{K} C(m+1+K, K-k) C(m+k, k)` -/
def R (m K : ℕ) : ℕ := ∑ k ∈ range (K + 1), (m + 1 + K).choose (K - k) * (m + k).choose k

/-- the Zeilberger certificate identity, for `i ≤ K` -/
theorem cert (m K i : ℕ) (hi : i ≤ K) :
    2 * ((m : ℤ) + K + 1) * (f m K i : ℤ) - ((K : ℤ) + 1) * (f m (K + 1) i : ℤ)
      = G m K (i + 1) - G m K i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  unfold f G
  rw [show i + j - i = j by omega, show i + j + 1 - i = j + 1 by omega,
    show i + j + 1 - (i + 1) = j by omega, show m + (i + j + 1) = m + (i + j) + 1 by omega,
    show m + (i + 1) = m + i + 1 by omega]
  have h1 := Nat.add_one_mul_choose_eq (m + (i + j)) j
  have h2 := Nat.choose_mul_succ_eq (m + (i + j)) j
  rw [show m + (i + j) + 1 - j = m + i + 1 by omega] at h2
  have h3 := Nat.add_one_mul_choose_eq (m + i) i
  have h1' : (((m + (i + j) + 1 : ℕ) : ℤ)) * ((m + (i + j)).choose j : ℤ)
      = ((m + (i + j) + 1).choose (j + 1) : ℤ) * (((j + 1 : ℕ)) : ℤ) := by exact_mod_cast h1
  have h2' : ((m + (i + j)).choose j : ℤ) * (((m + (i + j) + 1 : ℕ) : ℤ))
      = ((m + (i + j) + 1).choose j : ℤ) * (((m + i + 1 : ℕ)) : ℤ) := by exact_mod_cast h2
  have h3' : (((m + i + 1 : ℕ) : ℤ)) * ((m + i).choose i : ℤ)
      = ((m + i + 1).choose (i + 1) : ℤ) * (((i + 1 : ℕ)) : ℤ) := by exact_mod_cast h3
  push_cast at h1' h2' h3' ⊢
  linear_combination ((m + i).choose i : ℤ) * h1' + ((m + i).choose i : ℤ) * h2'
    + ((m + (i + j) + 1).choose j : ℤ) * h3'

/-- the recurrence `(K+1) D(K+1) = 2(m+K+1) D(K)` obtained by telescoping -/
theorem D_rec (m K : ℕ) : (K + 1) * D m (K + 1) = 2 * (m + K + 1) * D m K := by
  have hsum : ∑ i ∈ range (K + 1), (2 * ((m : ℤ) + K + 1) * (f m K i : ℤ)
      - ((K : ℤ) + 1) * (f m (K + 1) i : ℤ)) = G m K (K + 1) - G m K 0 := by
    rw [← Finset.sum_range_sub]
    apply Finset.sum_congr rfl
    intro i hi
    exact cert m K i (by simp at hi; omega)
  have hG0 : G m K 0 = 0 := by simp [G]
  have hGK : G m K (K + 1) = ((K : ℤ) + 1) * ((m + (K + 1)).choose (K + 1) : ℤ) := by
    unfold G
    rw [Nat.sub_self, Nat.choose_zero_right]
    push_cast
    ring
  have hD1 : (D m (K + 1) : ℤ)
      = ∑ i ∈ range (K + 1), (f m (K + 1) i : ℤ) + ((m + (K + 1)).choose (K + 1) : ℤ) := by
    unfold D
    rw [Finset.sum_range_succ]
    push_cast
    congr 1
    unfold f
    rw [Nat.sub_self, Nat.choose_zero_right]
    push_cast
    ring
  have hD : (D m K : ℤ) = ∑ i ∈ range (K + 1), (f m K i : ℤ) := by
    unfold D
    push_cast
    rfl
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hG0, hGK] at hsum
  have key : ((K : ℤ) + 1) * (D m (K + 1) : ℤ) = 2 * ((m : ℤ) + K + 1) * (D m K : ℤ) := by
    rw [hD1, hD]
    linear_combination (-1 : ℤ) * hsum
  exact_mod_cast key

/-- item 1: `Σ_{i=0}^{K} C(n+K-1, K-i) C(n+i-1, i) = 2^K C(n+K-1, K)` with `n = m+1` -/
theorem D_closed (m K : ℕ) : D m K = 2 ^ K * (m + K).choose K := by
  induction K with
  | zero => simp [D, f]
  | succ K ih =>
    have h1 := D_rec m K
    have h2 := Nat.add_one_mul_choose_eq (m + K) K
    rw [ih] at h1
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < K + 1)
    rw [h1, show m + (K + 1) = m + K + 1 by omega]
    calc 2 * (m + K + 1) * (2 ^ K * (m + K).choose K)
        = 2 ^ (K + 1) * ((m + K + 1) * (m + K).choose K) := by ring
      _ = 2 ^ (K + 1) * ((m + K + 1).choose (K + 1) * (K + 1)) := by rw [h2]
      _ = (K + 1) * (2 ^ (K + 1) * (m + K + 1).choose (K + 1)) := by ring

/-- `R(K+1) = R(K) + D(K+1)` (Pascal's rule) -/
theorem R_succ (m K : ℕ) : R m (K + 1) = R m K + D m (K + 1) := by
  have e1 : R m (K + 1) = (∑ k ∈ range (K + 1), (m + 1 + (K + 1)).choose (K + 1 - k)
      * (m + k).choose k) + (m + (K + 1)).choose (K + 1) := by
    unfold R
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.choose_zero_right, one_mul]
  have e2 : D m (K + 1) = (∑ k ∈ range (K + 1), (m + (K + 1)).choose (K + 1 - k)
      * (m + k).choose k) + (m + (K + 1)).choose (K + 1) := by
    unfold D f
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.choose_zero_right, one_mul]
  have hsplit : ∑ k ∈ range (K + 1), (m + 1 + (K + 1)).choose (K + 1 - k) * (m + k).choose k
      = R m K + ∑ k ∈ range (K + 1), (m + (K + 1)).choose (K + 1 - k) * (m + k).choose k := by
    unfold R
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ K := by simp at hk; omega
    rw [show K + 1 - k = (K - k) + 1 by omega, show m + 1 + (K + 1) = (m + 1 + K) + 1 by omega,
      Nat.choose_succ_succ', show m + (K + 1) = m + 1 + K by omega]
    ring
  rw [e1, e2, hsplit]
  ring

/-- item 2: `S(n,K) = R(n,K)` with `n = m+1` -/
theorem S_eq_R (m K : ℕ) : S m K = R m K := by
  induction K with
  | zero => simp [S, R]
  | succ K ih =>
    rw [R_succ, ← ih, D_closed]
    unfold S
    rw [Finset.sum_range_succ _ (K + 1)]
    ring

/-- item 3: the representation of `a n` for `n ≥ 1` -/
theorem a_eq_rep (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ k ∈ Finset.range (3 * n + 1),
      Nat.choose (4 * n) (3 * n - k) * Nat.choose (n + k - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hS : a (m + 1) = S m (3 * (m + 1)) := by
    unfold a S
    apply Finset.sum_congr rfl
    intro j _
    rw [show m + 1 + j - 1 = m + j by omega]
  rw [hS, S_eq_R]
  unfold R
  apply Finset.sum_congr rfl
  intro k _
  rw [show m + 1 + 3 * (m + 1) = 4 * (m + 1) by ring, show m + 1 + k - 1 = m + k by omega]

end A333562
