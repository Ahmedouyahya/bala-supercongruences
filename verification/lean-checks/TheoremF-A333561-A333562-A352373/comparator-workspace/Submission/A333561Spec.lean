import Submission.A333561Full

open Nat Finset

theorem oeis_333561_conjecture :
    ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] :=
  A333561_full
