import Submission.A376462Full

open Nat Finset

-- control: second congruence weakened to p^(3r-1), must be rejected by Comparator
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
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r - 1) : ℕ).cast]
    ) := by
  intro p n r hp hp5 hn hr
  have h := A376462_full p n r hp hp5 hn hr
  refine ⟨h.1, ?_⟩
  exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (Nat.sub_le _ _))) h.2
