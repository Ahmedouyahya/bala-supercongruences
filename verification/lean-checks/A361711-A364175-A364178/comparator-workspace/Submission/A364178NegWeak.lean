import Submission.A364178Full



-- control: weaker modulus, must be rejected by Comparator
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r - 1)] :=
  Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (oeis_364178_conjecture_0_full p n r hp h5 hn hr)
