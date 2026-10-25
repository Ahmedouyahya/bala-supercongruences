import Submission.A333565Full

open Nat Int BigOperators

-- control: weaker modulus p^(3k-1), must be rejected by Comparator
theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k - 1) : ℤ)] :=
  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333565_full p n k hp hp3 hn hk)
