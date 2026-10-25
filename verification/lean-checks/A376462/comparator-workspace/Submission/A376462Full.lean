import Submission.A376462First
import Submission.A376462ShiftMain

/-!
# A376462: both conjectured supercongruences

`oeis_376462_conjecture_0` (Formal Conjectures, `FormalConjectures/OEIS/Auto/376462_96154f2f.lean`,
commit 67338a1) for all primes `p ≥ 5`, `n ≥ 1`, `r ≥ 1`: the first conjunct is `A376462_first`
(`BalaCheck/A376462First.lean`), the second is `A376462_shifted` (`BalaCheck/A376462ShiftMain.lean`).
-/

theorem A376462_full :
  ∀ (p n r : ℕ),
    Nat.Prime p →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by
  intro p n r hp hp5 hn hr
  exact ⟨A376462_first p n r hp hp5 hn hr, A376462_shifted p n r hp hp5 hn hr⟩
