import Submission.A370092Odd
import Submission.A370092Two

/-!
# A370092, Part 4: assembly

The statement is taken from the Formal Conjectures file
`FormalConjectures/OEIS/Auto/370092_862cfcda.lean` (commit 67338a1), imported unchanged: the final
theorem is stated as `type_of% @oeis_370092_conjecture_0`. Period `P := φ(k)`, start `N := k + 2`.
-/

open Finset

namespace A370092

theorem A_periodic_mul (q : ℤ) (T N : ℕ) (hT : ∀ n, N ≤ n → q ∣ A (n + T) - A n) :
    ∀ c n, N ≤ n → q ∣ A (n + c * T) - A n := by
  intro c
  induction c with
  | zero => intro n _; simp
  | succ c ih =>
    intro n hn
    have h1 := hT (n + c * T) (by omega)
    have h2 := ih n hn
    rw [show n + (c + 1) * T = n + c * T + T by ring]
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

theorem A_periodic_dvd (q : ℤ) (T N M : ℕ) (hT : ∀ n, N ≤ n → q ∣ A (n + T) - A n)
    (hTM : T ∣ M) : ∀ n, N ≤ n → q ∣ A (n + M) - A n := by
  obtain ⟨c, rfl⟩ := hTM
  intro n hn
  rw [mul_comm]
  exact A_periodic_mul q T N hT c n hn

theorem prime_pow_dvd_A (k p j : ℕ) (hk : 2 < k) (hp : p.Prime) (hpk : p ^ j ∣ k) (n : ℕ)
    (hn : k + 2 ≤ n) : ((p ^ j : ℕ) : ℤ) ∣ A (n + Nat.totient k) - A n := by
  have hjk : j < k := by
    have h1 : p ^ j ≤ k := Nat.le_of_dvd (by omega) hpk
    have h2 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    omega
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · have hj1' : j = 1 := by omega
      subst hj1'
      have h4 : ∀ n, 3 ≤ n → ((2 ^ 1 : ℕ) : ℤ) ∣ A (n + 2) - A n := by
        intro n hn
        have := A_two n 0 (by omega)
        exact (show ((2 ^ 1 : ℕ) : ℤ) ∣ 2 ^ (0 + 2) by norm_num).trans this
      exact A_periodic_dvd _ 2 3 _ h4 (Nat.totient_even hk).two_dvd n (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have h4 : ∀ n, m + 3 ≤ n → ((2 ^ (m + 2) : ℕ) : ℤ) ∣ A (n + 2 ^ (m + 1)) - A n := by
        intro n hn; push_cast; exact A_two n m hn
      have hT : 2 ^ (m + 1) ∣ Nat.totient k := by
        have := Nat.totient_dvd_of_dvd hpk
        rw [show m + 2 = (m + 1) + 1 from rfl, Nat.totient_prime_pow_succ Nat.prime_two] at this
        simpa using this
      exact A_periodic_dvd _ _ (m + 3) _ h4 hT n (by omega)
  · have h4 : ∀ n, j ≤ n → ((p ^ j : ℕ) : ℤ) ∣ A (n + Nat.totient (p ^ j)) - A n :=
      fun n hn => A_odd p j n hp hp2 hn
    exact A_periodic_dvd _ _ j _ h4 (Nat.totient_dvd_of_dvd hpk) n (by omega)

theorem k_dvd (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : k + 2 ≤ n) :
    (k : ℤ) ∣ A (n + Nat.totient k) - A n := by
  rw [Int.natCast_dvd]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ k).mpr fun p j hp hpk => ?_
  exact Int.natCast_dvd.mp (prime_pow_dvd_A k p j hk hp hpk n hn)

end A370092

theorem A370092_full : ∀ (k : ℕ), 2 < k → ∃ P : ℕ, P ∣ Nat.totient k ∧ eventually_periodic (a_mod_k k) P := by
  intro k hk
  refine ⟨Nat.totient k, dvd_refl _, ?_⟩
  unfold eventually_periodic
  refine ⟨k + 2, fun n hn => ?_⟩
  unfold a_mod_k
  rw [A370092.a_num, A370092.a_num]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (A370092.k_dvd k hk n hn))
