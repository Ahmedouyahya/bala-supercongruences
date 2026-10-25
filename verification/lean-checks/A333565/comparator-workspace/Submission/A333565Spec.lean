import Submission.A333565Full

open Nat Int BigOperators

theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] :=
  A333565_full p n k hp hp3 hn hk
