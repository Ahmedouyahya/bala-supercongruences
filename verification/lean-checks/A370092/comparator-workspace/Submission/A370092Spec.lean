import Submission.A370092Full

open Finset Nat

theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P :=
  A370092_full k hk
