import Submission.A376462Classes

/-!
# A376462: the first conjectured supercongruence

The statement is the first conjunct of `oeis_376462_conjecture_0` in the Formal Conjectures file
`FormalConjectures/OEIS/Auto/376462_96154f2f.lean` (commit 67338a1), whose definitions
`A376462`, `a108625_aux` are imported unchanged.

Proof (`proofs/A376462-first-congruence.md`, §0–§3; `N = m p^r`, `M = m p^(r-1)`):
representation (1) (`rep`), split both indices by divisibility by `p` (`split_lev`), and the four
classes `classS`, `classK`, `classI`, `classB`.
-/

open Nat Finset

namespace A376462Proof

/-- `p^(3r) ∣ A376462(m p^r) - A376462(m p^(r-1))`. -/
theorem cong (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ (A376462 (m * p ^ r) : ℤ) - (A376462 (m * p ^ (r - 1)) : ℤ) := by
  haveI := Fact.mk hp
  have hsplit : ∀ f : ℕ → ℤ, ∑ k ∈ range (m * p ^ r + 1), f k
      = ∑ j ∈ range (m * p ^ (r - 1) + 1), f (p * j)
        + ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k), f k :=
    fun f => split_lev p m r hr f
  have e : (A376462 (m * p ^ r) : ℤ) - (A376462 (m * p ^ (r - 1)) : ℤ)
      = ∑ K ∈ range (m * p ^ (r - 1) + 1), ∑ I ∈ range (m * p ^ (r - 1) + 1),
          ((T (m * p ^ r) (p * K) (p * I) : ℤ) - (T (m * p ^ (r - 1)) K I : ℤ))
        + ∑ K ∈ range (m * p ^ (r - 1) + 1),
          ∑ i ∈ (range (m * p ^ r + 1)).filter (fun i => ¬ p ∣ i), (T (m * p ^ r) (p * K) i : ℤ)
        + ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k),
          ∑ I ∈ range (m * p ^ (r - 1) + 1), (T (m * p ^ r) k (p * I) : ℤ)
        + ∑ k ∈ (range (m * p ^ r + 1)).filter (fun k => ¬ p ∣ k),
          ∑ i ∈ (range (m * p ^ r + 1)).filter (fun i => ¬ p ∣ i), (T (m * p ^ r) k i : ℤ) := by
    rw [rep, rep]
    push_cast
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e]
  exact dvd_add (dvd_add (dvd_add (classS p hp5 m r hm hr) (classI p hp5 m r hm hr))
    (classK p hp5 m r hm hr)) (classB p m r)

end A376462Proof

theorem A376462_first : ∀ (p n r : ℕ), Nat.Prime p → 5 ≤ p → 0 < n → 0 < r → (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast] := by
  intro p n r hp hp5 hn hr
  have h := A376462Proof.cong p hp hp5 n r hn hr
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  push_cast
  exact h
