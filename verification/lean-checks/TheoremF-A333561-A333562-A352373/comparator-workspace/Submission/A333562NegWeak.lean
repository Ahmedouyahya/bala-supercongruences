import Submission.A333562Full

open Nat Finset

-- control: weaker modulus, must be rejected by Comparator
theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k - 1)] :=
  fun hp hp5 hn hk => Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333562_full p n k hp hp5 hn hk)
