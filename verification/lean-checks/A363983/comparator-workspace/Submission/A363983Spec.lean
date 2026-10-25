import Submission.A363983Full

open Nat Finset Int

theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] :=
  A363983_full p n r hp h_p_ge_5 hn hr
