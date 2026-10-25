import BalaCheck.A370092Formula

/-!
# A370092, Part 2: odd prime powers

For `q = p^α` (`p` an odd prime) and `n ≥ α`: `q ∣ A (n + φ q) - A n`.
-/

open Finset

namespace A370092

theorem prime_pow_dvd_term (p α n j : ℕ) (hp : p.Prime) (hn : α ≤ n) :
    ((p ^ α : ℕ) : ℤ) ∣ (j : ℤ) ^ n * ((j : ℤ) ^ Nat.totient (p ^ α) - 1) := by
  by_cases hpj : p ∣ j
  · apply dvd_mul_of_dvd_left
    have : p ^ α ∣ j ^ n := (pow_dvd_pow_of_dvd hpj α).trans (pow_dvd_pow j hn)
    exact_mod_cast this
  · apply dvd_mul_of_dvd_right
    have hcop : Nat.Coprime j (p ^ α) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj))
    have hmod := Nat.ModEq.pow_totient hcop
    have := Nat.modEq_iff_dvd.mp hmod.symm
    push_cast at this
    exact this

theorem odd_E_diff (p α n k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : α ≤ n) :
    ((p ^ α : ℕ) : ℤ) ∣ E k (n + Nat.totient (p ^ α)) - E k n := by
  have hb : ((p ^ α : ℕ) : ℤ) ∣ (E k (n + Nat.totient (p ^ α)) - E k n) * 2 ^ (k / 3) := by
    rw [mul_comm, mul_sub, E_spec, E_spec, D_sub_eq]
    exact fdiff_dvd _ _ _ (fun j => prime_pow_dvd_term p α n j hp hn)
  have hcop : Nat.Coprime (p ^ α) (2 ^ (k / 3)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcop' : IsCoprime ((p ^ α : ℕ) : ℤ) (2 ^ (k / 3)) := by
    have := Nat.isCoprime_iff_coprime.mpr hcop
    push_cast at this ⊢
    exact this
  exact hcop'.dvd_of_dvd_mul_right hb

/-- Part 2: odd prime powers. -/
theorem A_odd (p α n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : α ≤ n) :
    ((p ^ α : ℕ) : ℤ) ∣ A (n + Nat.totient (p ^ α)) - A n := by
  rw [A_sub_eq]
  exact dvd_sum fun k _ => dvd_mul_of_dvd_right (odd_E_diff p α n k hp hp2 hn) _

end A370092
