import Submission.A333561Full

open Nat Finset

-- control: weaker modulus, must be rejected by Comparator
theorem oeis_333561_conjecture :
    ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k - 1)] :=
  fun p n k hp hp5 hn hk => Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333561_full p n k hp hp5 hn hk)
