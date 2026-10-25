import Submission.A376462Full

open Nat Finset

theorem oeis_376462_conjecture_0 :
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
    ) :=
  A376462_full
