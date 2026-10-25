import Submission.Bridge

open Nat BigOperators Finset

theorem u_m_supercongruence_conjecture (m n r : ℕ) (hm : m > 0) (hn : n > 0) (hr : r > 0)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℤ)] :=
  BalaA352275.u_scale m n r hn hr p hp hp5
