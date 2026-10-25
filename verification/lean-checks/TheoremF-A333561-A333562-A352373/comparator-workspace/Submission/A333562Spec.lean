import Submission.A333562Full

open Nat Finset

theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] :=
  A333562_full p n k
