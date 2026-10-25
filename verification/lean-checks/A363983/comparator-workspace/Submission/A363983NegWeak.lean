import Submission.A363983Full

open Nat Finset Int

-- control: weaker modulus, must be rejected by Comparator
theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r - 1)] :=
  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A363983_full p n r hp h_p_ge_5 hn hr)
