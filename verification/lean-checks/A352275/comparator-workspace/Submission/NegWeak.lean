import Submission.Bridge

open Nat BigOperators Finset

/-- A true but weaker statement (modulus p^(3r-1)); the checker must reject it as not the challenge. -/
theorem u_m_supercongruence_conjecture (m n r : ℕ) (hm : m > 0) (hn : n > 0) (hr : r > 0)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r - 1) : ℤ)] :=
  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (BalaA352275.u_scale m n r hn hr p hp hp5)
