import BalaProofs.A364175

namespace Bench364175




open Real Nat Int

/--
A364175: $a(n) = \frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$.
The fractional factorial $x!$ is defined as $\Gamma(x+1)$.
This sequence is only conjecturally an integer sequence. We round the real-valued result to obtain a natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat


theorem a_zero : a 0 = 1 := by
  dsimp only [a]
  simp only [Nat.cast_zero, mul_zero, zero_add, Real.Gamma_one, mul_one, div_self (one_ne_zero : (1 : ℝ) ≠ 0), round_one, Int.toNat_one]



/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $r$.
Note: The expression $r-1$ is a natural number subtraction, which is safe since $r$ is positive.
-/
theorem oeis_364175_conjecture_0 (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have e : Bench364175.a = _root_.a := rfl
  rw [e]; exact _root_.oeis_364175_conjecture_0 p n r hp h_prime_ge_five hn hr

end Bench364175

#print axioms Bench364175.oeis_364175_conjecture_0
