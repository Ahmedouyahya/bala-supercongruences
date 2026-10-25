import Submission.BalaGeneralFull

namespace BalaGeneral

-- control: weaker modulus in the first theorem, must be rejected by Comparator
theorem bala_A352373_general (r s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRS r s (n * p ^ k) ≡ aRS r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k - 1)] :=
  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (full_A352373_general r s p hp hp5 n k hn hk)

theorem bala_A333715_general (r : ℕ) (s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRSn r s (n * p ^ k) ≡ aRSn r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] :=
  full_A333715_general r s p hp hp5 n k hn hk

end BalaGeneral
