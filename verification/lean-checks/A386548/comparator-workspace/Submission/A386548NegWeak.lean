import Submission.A386548Full

open Finset Nat BigOperators Int

theorem oeis_A386548_supercongruence_conjecture :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k - 1) : ℤ)] := by
  intro p hp hp5 n k hn hk
  exact Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A386548_full p hp hp5 n k hn hk)
