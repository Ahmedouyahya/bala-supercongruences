import Submission.A361711Full

open Nat Int Finset BigOperators

-- control: weaker modulus, must be rejected by Comparator
theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k - 1) : ℕ)] :=
  Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow _ (Nat.sub_le _ _))) (A361711_conjecture_full p hp h_geq_5 k hk)
