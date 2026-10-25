import FormalConjectures.OEIS.Auto.«376462_96154f2f»

/-!
# A376462, part 1: representation (1)

`proofs/A376462-first-congruence.md`, §0: with
`T(n;k,i) = C(n,k)² C(n+k,k) C(n,i)² C(2n-k-i, n)`,
`A376462 n = Σ_{k ≤ n} Σ_{i ≤ n} T(n;k,i)`.

The definitions `A376462` and `a108625_aux` are used from the Formal Conjectures file
`FormalConjectures/OEIS/Auto/376462_96154f2f.lean`, imported unchanged.
-/

open Nat Finset

namespace A376462Proof

/-- The summand of representation (1): `C(n,k)² C(n+k,k) C(n,i)² C(2n-k-i, n)`. -/
def T (n k i : ℕ) : ℕ :=
  n.choose k ^ 2 * (n + k).choose k * n.choose i ^ 2 * (2 * n - k - i).choose n

/-- `A108625(n, n-k) = Σ_{i ≤ n} C(n,i)² C(2n-k-i, n)` for `k ≤ n`. -/
lemma aux_eq (n k : ℕ) (hk : k ≤ n) :
    a108625_aux n (n - k) = ∑ i ∈ range (n + 1), n.choose i ^ 2 * (2 * n - k - i).choose n := by
  unfold a108625_aux
  rw [← Finset.sum_range_add_sum_Ico _ (show n - k + 1 ≤ n + 1 by omega)]
  have h0 : ∑ i ∈ Ico (n - k + 1) (n + 1), n.choose i ^ 2 * (2 * n - k - i).choose n = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega : 2 * n - k - i < n), mul_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  congr 1
  rw [show n + (n - k) - i = (n - k - i) + n by omega,
    show 2 * n - k - i = (n - k - i) + n by omega]
  exact Nat.choose_symm_add

/-- **Representation (1).** -/
lemma rep (n : ℕ) : A376462 n = ∑ k ∈ range (n + 1), ∑ i ∈ range (n + 1), T n k i := by
  unfold A376462
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [aux_eq n k (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold T
  ring

end A376462Proof
