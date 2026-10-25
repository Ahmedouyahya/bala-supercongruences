import Submission.A370092Full

open Finset Nat

-- control: weaker statement (period divides 2·φ(k)), must be rejected by Comparator
theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ 2 * totient k ∧ eventually_periodic (a_mod_k k) P := by
  obtain ⟨P, hP, hper⟩ := A370092_full k hk
  exact ⟨P, dvd_mul_of_dvd_right hP 2, hper⟩
