import Submission.A352373Full

open scoped BigOperators Nat Finset Int

-- control: weaker modulus, must be rejected by Comparator
theorem oeis_a352373_supercongruence :
    ∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),
  ∀ (n : ℕ) (hn_pos : 0 < n),
  ∀ (k : ℕ) (hk_pos : 0 < k),
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k - 1)] :=
  fun p hp hp5 n hn k hk => Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A352373_full p hp hp5 n hn k hk)
