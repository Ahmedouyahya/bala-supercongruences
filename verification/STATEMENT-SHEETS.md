# Statement sheets for the human check

Purpose: a person with mathematical training reads each Lean statement below against Bala's text and confirms that it says the same thing. This is the one check a computer cannot do: Lean proves exactly what is written, so if a statement said something different from Bala's conjecture, the proof would be correct about the wrong thing.

How to read the Lean text: `C(n,k)` is `Nat.choose n k`; natural-number subtraction stops at 0 (5 − 7 = 0); `Int.toNat` maps negative integers to 0; `a ≡ b [MOD m]` (natural numbers) and `a ≡ b [ZMOD m]` (integers) mean m divides a − b. The theorems named a_zero, a_one, … inside some target files are sample facts of the benchmark, some unproved (`sorry`); our proofs never use them.

Bala's text is from the stored OEIS copy (`statements/oeis_bala_records.json`, revision and date given per entry); re-check the live OEIS page before publishing, since entries change.

## A352275

**OEIS name.** a(0) = 1 and a(n) = Sum_{k = 0..2*n} n/(n + 2*k)*binomial(n + 2*k,k) for n >= 1.

**Bala's conjecture** (OEIS revision 19, 2022-10-23):

> Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for primes p >= 5 and positive integers n and r.
> Then we conjecture that each sequence u_m satisfies the above supercongruences. This is the case m = 2. See A333093 (case m = 1) and A352276 case (m = 3).

**Lean target** (`statements/lean-targets/352275_4b1f2230.lean`, theorem `u_m_supercongruence_conjecture`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A352275: $a(0) = 1$ and
$$a(n) = \sum_{k = 0}^{2n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (2 * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 4 := by
  norm_num[a]
  norm_num+decide only[Finset.sum_range_succ,Nat.choose]

theorem a_two : a 2 = 64 := by
  inhabit ℝ
  delta a
  norm_num+decide only[Nat.choose,if_true, Finset.sum_range_succ, if_false]

theorem a_three : a 3 = 1429 := by
  delta a
  norm_num+decide only[Nat.choose, if_false, true, Finset.sum_range_succ]

/--
More generally, for $m$ a positive integer, define a sequence $u_m$ by setting
$$u_m(n) = \sum_{k = 0}^{m n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
We set $u_m(0) = 1$ to match the sequence $A352275 = u_2$.
-/
noncomputable def u (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat

/--
oeis_352275_conjecture_2:
Then we conjecture that each sequence $u_m$ satisfies the above supercongruences.
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$ hold for primes $p \ge 5$ and positive integers $n$ and $r$.
This is equivalent to: $u_m(n p^r) \equiv u_m(n p^{r-1}) \pmod{p^{3r}}$ holds for primes $p \ge 5$ and positive integers $m, n, r$.
-/
theorem u_m_supercongruence_conjecture (m n r : ℕ) (hm : m > 0) (hn : n > 0) (hr : r > 0)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℤ)] := by
  sorry
```

**Plain-English reading.** For every m ≥ 1, every n ≥ 1, every r ≥ 1 and every prime p ≥ 5: u_m(n·p^r) ≡ u_m(n·p^(r−1)) modulo p^(3r), as integers. Here u_m(n) = Σ_{k=0}^{mn} n/(n+2k)·C(n+2k,k) for n ≥ 1, and A352275 = u_2. This is Bala's general conjecture for every u_m, not only A352275.

**Lean conventions that matter.** Each term n/(n+2k)·C(n+2k,k) is computed in ℚ, then `Rat.floor`, then `toNat`. Our proof shows each term is the non-negative integer C(n+2k−1,k) − C(n+2k−1,k−1), so floor and toNat change nothing. u_m(0) := 1 is a convention; n·p^r ≥ 1, so it never enters.

**Link to Bala's definition.** The target's u is Bala's definition (with the convention above).

**Data check.** u_1, u_2, u_3 vs A333093, A352275, A352276 b-files (n ≤ 22, 400, 475): 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/A352275/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A361711

**OEIS name.** a(1) = 1 and a(n) = Sum_{k = 0..n-2} (-1)^k * binomial(n,k)^2 * binomial(n-2,k) for n >= 2.

**Bala's conjecture** (OEIS revision 20, 2023-03-26):

> Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.

**Lean target** (`statements/lean-targets/361711_10bc62a7.lean`, theorem `A361711_conjecture`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat Int Finset BigOperators

/--
A361711: $a(1) = 1$ and $a(n) = \sum_{k = 0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$ for $n \ge 2$.
-/
def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    -- $n-2$ is the upper limit of summation.
    let m : ℕ := N - 2

    -- The sum is over k from 0 to m, which is Finset.range (m + 1).
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

/--
A361711 Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.
-/
theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  sorry
```

**Plain-English reading.** For every prime p ≥ 5 and k ≥ 1: a(p^k) ≡ a(p^(k−1)) modulo p^(3k), as integers. (Bala's conjecture is only about n = 1, i.e. a(p^k).)

**Lean conventions that matter.** Defined in ℤ; a(0) := 0 is a convention outside the OEIS offset (p^k ≥ 1, so it never enters). `m := N − 2` is safe since N ≥ 2 in that branch.

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 26 b-file terms (n = 1..26): 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/A361711-A364175-A364178/ (and lean/README.md)`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A363983

**OEIS name.** a(n) = Sum_{k = floor((n+1)/2)..n} (-1)^(n+k)*binomial(n,k)*binomial(n+k-1,k)*binomial(2*k,n).

**Bala's conjecture** (OEIS revision 18, 2023-07-09):

> The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences.

**Lean target** (`statements/lean-targets/363983_3f7e4c53.lean`, theorem `oeis_A363983_conjecture_supercongruence`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A363983: The sequence defined by
$$a(n) = \sum_{k = \lfloor\frac{n+1}{2}\rfloor}^n (-1)^{n+k} \binom{n}{k} \binom{n+k-1}{k} \binom{2k}{n}$$
The sum is implemented over $k=0$ to $n$ in $\mathbb{Z}$ and then cast to $\mathbb{N}$, as the sequence is known to be non-negative.
Note: The sum limits in the OEIS sequence definition are $\lfloor(n+1)/2\rfloor \le k \le n$. The definition below, summing $k=0$ to $n$, is equivalent because $\binom{2k}{n}=0$ for $2k < n$, i.e. $k < n/2$. The term $\binom{n+k-1}{k}$ is zero for $k < 0$ (vacuously true here) or when $n+k-1 < k$ and $k \ne 0$, i.e., $n-1 < 0$, or $n=0$ and $k>0$. For $n=0$, the only term is $k=0 \Rightarrow 1$. For $n>0$, $n+k-1 \ge k$ holds for non-negative $k$, and all terms for $k < \lceil n/2 \rceil$ are correct either way. Given the OEIS formula simplifies to the $k=0$ to $n$ sum via the identity shown in the comments, this definition is a standard equivalent form.
-/
def A363983 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k : ℕ =>
    -- The expression must result in ℤ due to the alternating sign.
    let sign_factor : ℤ := (-1) ^ (n + k)
    -- Binomial coefficients (Nat.choose) are implicitly coerced to ℤ for multiplication.
    -- (n + k - 1).choose k is written as ((n + k).pred.choose k) in Mathlib's Nat.choose syntax.
    let term_val : ℤ := (n.choose k) * ((n + k).pred.choose k) * ((2 * k).choose n)
    sign_factor * term_val
  ).toNat

/-- oeis_363983_conjecture_0: The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences. -/
theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, r ≥ 1: a(n·p^r) ≡ a(n·p^(r−1)) modulo p^(3r), as integers.

**Lean conventions that matter.** The sum is over k = 0..n instead of ⌊(n+1)/2⌋..n (the extra terms vanish because C(2k, n) = 0 for 2k < n); `(n+k).pred` is n+k−1; the alternating sum is computed in ℤ and then `toNat`. Our proof shows the sum is positive for n ≥ 1, so toNat changes nothing.

**Link to Bala's definition.** The target is Bala's definition (the extra zero terms aside).

**Data check.** 19 b-file terms (n = 0..18): 0 mismatches; positivity for n ≤ 800.

**Proof status.** done. Evidence: `verification/lean-checks/A363983/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A364175

**OEIS name.** a(n) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!).

**Bala's conjecture** (OEIS revision 16, 2026-07-22):

> Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
> The integrality conjecture is true. See Links. - _David Radcliffe_, Jul 19 2026

**Lean target** (`statements/lean-targets/364175_1518df7a.lean`, theorem `oeis_364175_conjecture_0`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

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

-- The proofs for a_one, a_two, and a_three below rely on numerical evaluation
-- and complex simplification rules which are not straightforward to port directly
-- or fix, but they compile when using powerful tactics like `norm_num` or if
-- the user environment had additional custom lemmas. Since they are not the
-- main object of the task, we keep them as they are, assuming the provided
-- environment could handle them, or simplify them to `sorry` for robustness.
-- Since only a_zero failed, we fix that and proceed.

theorem a_one : a 1 = 36 := by sorry

theorem a_two : a 2 = 3564 := by sorry

theorem a_three : a 3 = 408408 := by sorry


/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $r$.
Note: The expression $r-1$ is a natural number subtraction, which is safe since $r$ is positive.
-/
theorem oeis_364175_conjecture_0 (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, r ≥ 1: a(n·p^r) ≡ a(n·p^(r−1)) modulo p^(3r), as natural numbers.

**Lean conventions that matter.** a(n) is the real number (6n)!·(2n/3)!/((3n)!·(2n)!·(5n/3)!) with x! = Γ(x+1), rounded to the nearest integer, then toNat. Our proof shows this real number is exactly the integer 3^n(6n)!/((3n)!(2n)!Π_{j=1}^n(2n+3j)) (theorem a_eq_B175), so rounding changes nothing (integrality is Radcliffe's theorem, here proved in Lean).

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 15 b-file terms: 0 mismatches; the Γ definition agrees with the integer formula for n ≤ 40 (high precision).

**Proof status.** done. Evidence: `verification/lean-checks/A361711-A364175-A364178/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A364178

**OEIS name.** a(n) = (10*n)!*(3*n)!*(n/2)!/((6*n)!*(5*n)!*(3*n/2)!*n!).

**Bala's conjecture** (OEIS revision 15, 2025-11-05):

> Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.

**Lean target** (`statements/lean-targets/364178_4c681d65.lean`, theorem `oeis_364178_conjecture_0`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Real
open Nat

/--
A364178: The conjecturally integral sequence
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$
where $x! := \Gamma(x+1)$ for real $x$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat


/-- A364178 Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r. -/
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
by sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, r ≥ 1: a(n·p^r) ≡ a(n·p^(r−1)) modulo p^(3r), as natural numbers.

**Lean conventions that matter.** a(n) is (10n)!(3n)!(n/2)!/((6n)!(5n)!(3n/2)!n!) with x! = Γ(x+1), rounded, then toNat. Our proof shows it equals the integer 2^n(10n)!(3n)!/((6n)!(5n)!n!Π_{j=1}^n(n+2j)) (theorem a_eq_B178), which includes the integrality of A364178.

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 13 b-file terms: 0 mismatches; the Γ definition agrees with the integer formula for n ≤ 40 (high precision).

**Proof status.** done. Evidence: `verification/lean-checks/A361711-A364175-A364178/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A386548

**OEIS name.** a(n) = [x^n] ((1 - x)/(1 - x + x^2))^n.

**Bala's conjecture** (OEIS revision 15, 2025-08-03):

> Conjecture: the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for all primes p >= 5 and all positive integers n and k.

**Lean target** (`statements/lean-targets/386548_8788c4f8.lean`, theorem `oeis_A386548_supercongruence_conjecture`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Finset Nat BigOperators Int

/--
A386548: The sequence $a(n) = [x^n] \left( \frac{1 - x}{1 - x + x^2} \right)^n$.
This is formally defined by the combinatorial formula $a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} (-1)^k \binom{n+k-1}{k} \binom{n-k-1}{n-2k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n / 2 + 1))
    (fun k ↦
      let sign : ℤ := if k % 2 = 0 then 1 else -1
      -- Nat.choose handles binomial(n, k) = 0 if k > n due to truncated subtraction on Nat.
      let term1 : ℕ := (n + k - 1).choose k
      let term2 : ℕ := (n - k - 1).choose (n - 2 * k)
      sign * (term1 : ℤ) * (term2 : ℤ))

/--
Conjecture: the stronger supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{2k}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $k$.
-/
theorem oeis_A386548_supercongruence_conjecture :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k) : ℤ)] :=
by sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, k ≥ 1: a(n·p^k) ≡ a(n·p^(k−1)) modulo p^(2k) (squared, not cubed), as integers.

**Lean conventions that matter.** The target uses the formula Σ_{k ≤ n/2} (−1)^k C(n+k−1,k)·C(n−k−1,n−2k) from the entry, with natural subtraction (safe for n ≥ 1 and k ≤ n/2).

**Link to Bala's definition.** Our Lean proof (lean/BalaProofs/A386548Series.lean) shows a(N) = [x^N] of (1+X)^(−N) with X replaced by U = x²/(1−x) (lemma `coeff_subst_U`, with `Bser_mul`: Bser·(1+X)^N = 1), and (1 + x²/(1−x))^(−1) = (1−x)/(1−x+x²); so the target formula is Bala's definition [x^n]((1−x)/(1−x+x²))^n, for n ≥ 1.

**Data check.** 32 b-file terms: 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/A386548/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A370092

**OEIS name.** a(0) = 1, a(n) = (-1)^n + (1/2) * Sum_{j=1..n} (1-(-1)^j-(-2)^j) * binomial(n,j) * a(n-j) for n > 0.

**Bala's conjecture** (OEIS revision 41, 2025-11-19):

> Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k). For example, modulo 10 we obtain the sequence [1, 1, 3, 6, 5, 6, 3, 6, 5, 6, 3, 6, 5, 6, 3, 6, 5, 6, ...] with an apparent period of 4 beginning at a(2). See A000670 for a more general conjecture. - _Peter Bala_, Feb 16 2024

**Lean target** (`statements/lean-targets/370092_862cfcda.lean`, theorem `oeis_370092_conjecture_0`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A370092: $a(0) = 1$,
$$a(n) = (-1)^n + \frac{1}{2} \sum_{j=1}^n (1-(-1)^j-(-2)^j) \binom{n}{j} a(n-j) \quad \text{for } n > 0$$
The sequence is defined in $\mathbb{Q}$ to directly translate the recurrence relation.
The terms are conjectured to be integers.
-/
noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    -- The sum is over j from 1 to m_plus_one. k runs from 0 to m.
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1 -- j is the index for the sum

      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j

      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val


theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 3 := by
  sorry

theorem a_three : a 3 = 16 := by
  sorry


-- We formally define an eventually periodic sequence.
/-- A sequence `f` is eventually periodic with period `P` if after some index `N`, `f(n + P) = f(n)`. -/
def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

/--
The reduction of `a n` modulo `k`. Since all terms of `a n` are integers, we take the
numerator of the rational number representation, which is the integer value, and reduce it modulo `k`.
This requires `k > 0`, which is guaranteed by `2 < k`.
-/
noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

/--
%C A370092 Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).
-/
theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  sorry
```

**Plain-English reading.** For every k > 2 there is a P dividing φ(k) such that, from some index on, a(n+P) ≡ a(n) modulo k. (A minimal period divides every period, so this is Bala's 'eventually periodic with the period dividing φ(k)'.)

**Lean conventions that matter.** a(n) is defined in ℚ by Bala's recurrence; `a_mod_k` reduces the numerator of a(n) modulo k. Our proof shows every a(n) is an integer, so the numerator is a(n) itself (theorem a_num). P = 0 is impossible (0 ∣ φ(k) would need φ(k) = 0), so there is no trivial loophole; the proof uses P = φ(k).

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 201 b-file terms (n = 0..200): 0 mismatches; all terms integers for n ≤ 400.

**Proof status.** done. Evidence: `verification/lean-checks/A370092/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A333561

**OEIS name.** a(n) = Sum_{j = 0..2*n} binomial(n+j-1,j)*2^j.

**Bala's conjecture** (OEIS revision 25, 2026-08-23):

> We conjecture that this sequence satisfies the supercongruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Some examples are given below.

**Lean target** (`statements/lean-targets/333561_b286c526.lean`, theorem `oeis_333561_conjecture`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A333561: $a(n) = \sum_{k = 0}^{2n} \binom{3n}{2n-k}\binom{n+k-1}{k}$.
This is an equivalent identity conjectured in the OEIS entry, which may resolve issues with the automated checker.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (2 * n + 1)) fun k : ℕ =>
    Nat.choose (3 * n) (2 * n - k) * Nat.choose (n + k - 1) k


theorem a_zero : a 0 = 1 := by
  simp [a, range_one, choose_zero_right, choose_self, mul_one]

theorem a_one : a 1 = 7 := by
  calc
    a 1 = Finset.sum (Finset.range 3) (fun k : ℕ => choose 3 (2 - k) * choose (1 + k - 1) k) := rfl
    _ = (choose 3 2 * choose 0 0) + (choose 3 1 * choose 1 1) + (choose 3 0 * choose 2 2) := by sorry -- Simplified proof is getting complex, let's stick to sorrys for example checks
    _ = 7 := by sorry -- We must keep the focus on the conjecture formalization

theorem a_two : a 2 = 129 := by
  sorry

theorem a_three : a 3 = 2815 := by
  sorry


/-- We conjecture that this sequence satisfies the supercongruences
a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k.
-/
theorem oeis_333561_conjecture :
  ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] :=
by sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, k ≥ 1: a(n·p^k) ≡ a(n·p^(k−1)) modulo p^(3k), as natural numbers.

**Lean conventions that matter.** The target's `a` is NOT Bala's definition but the equivalent formula Σ_{k≤2n} C(3n,2n−k)·C(n+k−1,k) (its docstring says so). Natural subtraction is safe on the summation range.

**Link to Bala's definition.** Bala's definition is a(n) = Σ_{j≤2n} C(n+j−1,j)·2^j. We therefore also prove the congruence for that definition directly (`A333561Oeis.aOEIS_supercongruence`), linking the two by a proved identity.

**Data check.** 18 b-file terms: 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/TheoremF-A333561-A333562-A352373/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A333562

**OEIS name.** a(n) = Sum_{j = 0..3*n} binomial(n+j-1,j)*2^j.

**Bala's conjecture** (OEIS revision 18, 2026-08-24):

> We conjecture that this sequence satisfies the congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Some examples are given below.

**Lean target** (`statements/lean-targets/333562_2eccaf4c.lean`, theorem `oeis_333562_conjecture_0_congruence`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A333562: $a(n) = \sum_{j = 0}^{3n} \binom{n+j-1}{j} 2^j$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (3 * n + 1)) fun j =>
    (n + j - 1).choose j * (2 ^ j)


theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 15 := by sorry
theorem a_two : a 2 = 769 := by sorry
theorem a_three : a 3 = 47103 := by sorry

/--
We conjecture that this sequence satisfies the congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, k ≥ 1: a(n·p^k) ≡ a(n·p^(k−1)) modulo p^(3k), as natural numbers.

**Lean conventions that matter.** a(n) = Σ_{j≤3n} C(n+j−1,j)·2^j with natural subtraction (safe for n ≥ 1).

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 16 b-file terms: 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/TheoremF-A333561-A333562-A352373/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A352373

**OEIS name.** a(n) = [x^n] ( 1/((1 - x)^2*(1 - x^2)) )^n for n >= 1.

**Bala's conjecture** (OEIS revision 24, 2026-01-06):

> Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for all primes p >= 5 and positive integers n and k.
> Conjecture: for each r and s the above supercongruences hold for the sequence a(r,s;n) for n >= 1.

**Lean target** (`statements/lean-targets/352373_a1d5fa75.lean`, theorem `oeis_a352373_supercongruence`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open scoped BigOperators Nat Finset Int

/--
A352373: $a(n) = [x^n] \left( \frac{1}{(1 - x)^2(1 - x^2)} \right)^n$ for $n \ge 1$.
The sequence is explicitly given by the combinatorial sum:
$$a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} \binom{3n-2k-1}{n-2k} \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let n' := n
  Finset.sum (Finset.range (n' / 2 + 1)) fun k =>
    let term1_top := 3 * n' - 2 * k - 1
    let term1_bot := n' - 2 * k
    let term2_top := n' + k - 1
    let term2_bot := k
    (term1_top.choose term1_bot) * (term2_top.choose term2_bot)

lemma a_one : a 1 = 2 := by rfl
lemma a_two : a 2 = 12 := by rfl
lemma a_three : a 3 = 74 := by rfl
lemma a_four : a 4 = 484 := by rfl

/--
A352373 Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
hold for all primes p >= 5 and positive integers n and k.
-/
theorem oeis_a352373_supercongruence :
  ∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),
  ∀ (n : ℕ) (hn_pos : 0 < n),
  ∀ (k : ℕ) (hk_pos : 0 < k),
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] :=
by sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, k ≥ 1: a(n·p^k) ≡ a(n·p^(k−1)) modulo p^(3k), as integers.

**Lean conventions that matter.** The target uses the entry's sum Σ_{k≤n/2} C(3n−2k−1,n−2k)·C(n+k−1,k), with a(0) := 0 (never used). Natural subtraction is safe for n ≥ 1, k ≤ n/2.

**Link to Bala's definition.** Our proof shows the sum equals [x^n](1/((1−x)²(1−x²)))^n, Bala's definition (theorem TF.A_neg_one_neg_three).

**Data check.** 300 b-file terms: 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/TheoremF-A333561-A333562-A352373/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A333565

**OEIS name.** O.g.f.: (1 + 4*x)/((1 + x)*sqrt(1 - 8*x)).

**Bala's conjecture** (OEIS revision 19, 2021-10-06):

> We conjecture that this sequence satisfies the stronger congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 3 and positive integers n and k. The particular case when n = k = 1 follows from the corresponding result for A333564. Some examples of these congruences are given below.

**Lean target** (`statements/lean-targets/333565_757e3efd.lean`, theorem `oeis_A333565_conjecture_strong_gauss_congruence`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports

open Nat Int BigOperators

/--
A333565: The coefficients of the ordinary generating function $\frac{1 + 4x}{(1 + x)\sqrt{1 - 8x}}$.
The $n$-th term $a(n)$ is the coefficient of $x^n$, derived via convolution.
Let $b_m = 2^m \binom{2m}{m}$ be the coefficients of $1/\sqrt{1-8x}$, and $d_n = \sum_{k=0}^n (-1)^k b_{n-k}$ be the coefficients of $1/((1+x)\sqrt{1-8x})$. Then $a_n = d_n + 4 d_{n-1}$.
-/
def A333565 (n : ℕ) : ℕ :=
  -- $b_m = 2^m \binom{2m}{m}$ as an integer value. We use ⇑ for coercion from ℕ to ℤ.
  let b_coeff (m : ℕ) : ℤ := (2 ^ m * (2 * m).choose m : ℕ)

  -- $d_n$ coefficient via convolution. The sum goes from 0 to n.
  let d_coeff (n_idx : ℕ) : ℤ :=
    (Finset.range (n_idx + 1)).sum fun k =>
      (-1 : ℤ) ^ k * b_coeff (n_idx - k)

  -- $a_n = d_n + 4 d_{n-1}$. We handle the $d_{-1}=0$ case explicitly.
  let a_n_int : ℤ := d_coeff n + 4 * if n = 0 then 0 else d_coeff (n - 1)

  -- The result is guaranteed to be a natural number.
  a_n_int.toNat

-- The provided simple theorems are kept as placeholders.
theorem a_zero : A333565 0 = 1 := by sorry
theorem a_one : A333565 1 = 7 := by sorry
theorem a_two : A333565 2 = 33 := by sorry
theorem a_three : A333565 3 = 223 := by sorry

/--
We conjecture that this sequence satisfies the stronger congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 3$ and positive integers $n$ and $k$.
-/
theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] :=
  by sorry
```

**Plain-English reading.** For every prime p ≥ 3 (including 3) and n, k ≥ 1: a(n·p^k) ≡ a(n·p^(k−1)) modulo p^(3k), as integers.

**Lean conventions that matter.** a(n) = (d_n + 4d_{n−1}).toNat with b_m = 2^m·C(2m,m) and d_n = Σ_k (−1)^k b_{n−k}. Our proof shows the value is 2B(n) − (−1)^n ≥ 1, so toNat changes nothing.

**Link to Bala's definition.** Bala defines A333565 by its o.g.f. (1+4x)/((1+x)√(1−8x)). The target's convolution follows from 2^m C(2m,m) = [x^m](1−8x)^(−1/2), a classical identity that is not formalised here; the data check covers it.

**Data check.** 23 b-file terms: 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/A333565/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

## A376462

**OEIS name.** a(n) = Sum_{k = 0..n} binomial(n, k)^2*binomial(n+k, k)*A108625(n, n-k).

**Bala's conjecture** (OEIS revision 16, 2026-09-04):

> We conjecture that the present sequence satisfies the same pair of supercongruences. Some examples are given below.

**Lean target** (`statements/lean-targets/376462_96154f2f.lean`, theorem `oeis_376462_conjecture_0`, licence header omitted):

```lean
import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A helper function for the $A108625$ array:
$$A108625(n, k) = \sum_{i=0}^k \binom{n}{i}^2 \binom{n+k-i}{k-i}$$
-/
noncomputable def a108625_aux (n k : ℕ) : ℕ :=
  (range (k + 1)).sum fun i =>
    (n.choose i) ^ 2 * ((n + k - i).choose (k - i))

/--
A376462: $a(n) = \sum_{k = 0..n} \binom{n}{k}^2 \binom{n+k}{k} A108625(n, n-k)$.
-/
noncomputable def A376462 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))


theorem a_zero : A376462 0 = 1 := by
  constructor

theorem a_one : A376462 1 = 5 := by
  rfl

theorem a_two : A376462 2 = 109 := by
  subsingleton

theorem a_three : A376462 3 = 3317 := by
  econstructor

/--
We conjecture that the present sequence satisfies the same pair of supercongruences
as the Apéry numbers A005258. Specifically, for all primes $p \ge 5$ and all
positive integers $n$ and $r$:
1) $A(n p^r) \equiv A(n p^{r-1}) \pmod{p^{3r}}$
2) $A(n p^r - 1) \equiv A(n p^{r-1} - 1) \pmod{p^{3r}}$
-/
theorem oeis_376462_conjecture_0 :
  ∀ (p n r : ℕ),
    Nat.Prime p →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by sorry
```

**Plain-English reading.** For every prime p ≥ 5 and n, r ≥ 1, BOTH: a(n·p^r) ≡ a(n·p^(r−1)) and a(n·p^r − 1) ≡ a(n·p^(r−1) − 1), modulo p^(3r), as integers.

**Lean conventions that matter.** Bala's definition with A108625 written out; natural subtraction n·p^r − 1 is safe since n·p^r ≥ 1.

**Link to Bala's definition.** The target is Bala's definition.

**Data check.** 19 b-file terms (n = 0..18): 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/A376462/`.

**Reviewer:** statement matches Bala's text?  ☐ yes  ☐ no  — notes:

---

---

## Bala's general conjectures on A352373 and A333715 (no benchmark target)

**Bala's text** (OEIS A352373, revision 24, 2026-01-06):

> Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for all primes p >= 5 and positive integers n and k.
> More generally, let r and s be integers and define a sequence (a(r,s;n))n>=1 by a(r,s;n) = [x^n] ( (1 + x)^r * (1 - x)^s )^n.
> Conjecture: for each r and s the above supercongruences hold for the sequence a(r,s;n) for n >= 1.

(OEIS A333715, revision 35, 2026-08-05):

> We conjecture that a(n) satisfies the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k.
> The same congruences may hold more generally for the sequences a(r,s,n) := [x^(r*n)]( (1 + x)/(1 - x) )^(s*n), r a positive integer and s an integer. This is the case a(3,1,n).

**Lean statements** (written by the authors from the text above; `lean/BalaProofs/BalaGeneral.lean`, namespace `BalaGeneral`, `open PowerSeries`):

```lean
/-- Bala's `a(r,s;n) = [x^n] ((1 + x)^r (1 - x)^s)^n` (OEIS A352373). -/
def aRS (r s : ℤ) (n : ℕ) : ℤ :=
  coeff n ((binomialSeries ℤ r * rescale (-1) (binomialSeries ℤ s)) ^ n)

/-- Bala's `a(r,s,n) = [x^(r n)] ((1 + x)/(1 - x))^(s n) = [x^(r n)] ((1 + x)^s (1 - x)^(-s))^n`
(OEIS A333715). -/
def aRSn (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) ((binomialSeries ℤ s * rescale (-1) (binomialSeries ℤ (-s))) ^ n)

/-- **Bala's general conjecture on OEIS A352373**, for primes `p ≥ 5`: for all integers `r`, `s`,
`a(r,s;n p^k) ≡ a(r,s;n p^(k-1)) (mod p^(3k))` for all `n, k ≥ 1`. -/
theorem bala_A352373_general (r s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRS r s (n * p ^ k) ≡ aRS r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := ...

/-- **Bala's general conjecture on OEIS A333715**, for primes `p ≥ 5`: for every `r ≥ 0` and every
integer `s`, `a(r,s,n p^k) ≡ a(r,s,n p^(k-1)) (mod p^(3k))` for all `n, k ≥ 1`
(Bala states it for `r ≥ 1`). -/
theorem bala_A333715_general (r : ℕ) (s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRSn r s (n * p ^ k) ≡ aRSn r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := ...
```

**Plain-English reading.** (1) For all integers r, s, every prime p ≥ 5 and n, k ≥ 1: a(r,s;n·p^k) ≡ a(r,s;n·p^(k−1)) modulo p^(3k), where a(r,s;n) = [x^n]((1+x)^r(1−x)^s)^n. (2) For every r ≥ 0 (Bala: r ≥ 1), every integer s, every prime p ≥ 5 and n, k ≥ 1: a(r,s,n·p^k) ≡ a(r,s,n·p^(k−1)) modulo p^(3k), where a(r,s,n) = [x^(rn)]((1+x)/(1−x))^(sn).

**Lean conventions that matter.** `binomialSeries ℤ t` is Mathlib's power series (1+x)^t for an integer t (coefficients `Ring.choose t k`, the generalized binomial coefficient); `rescale (-1)` substitutes −x for x, so `rescale (-1) (binomialSeries ℤ s)` is (1−x)^s. ((1+x)/(1−x))^(sn) is written as ((1+x)^s(1−x)^(−s))^n, which is the same power series. Both theorems are stated as integer congruences.

**Link to Bala's definition.** The definitions are Bala's formulas written with Mathlib's power series. As a check, `aRS (-1) (-3) n` is proved equal to the benchmark's definition of A352373 for n ≥ 1 (`BalaGeneralCheck.lean`).

**Data check.** The Python mirror of both definitions agrees with the OEIS data of every sequence Bala names (A000984, A001700 with offset 1, A002003, A091527, A119259, A156894, A165817, A234839, A348410, A351857, A352373; A333715, A002003, A103885): 0 mismatches.

**Proof status.** done. Evidence: `verification/lean-checks/BalaGeneral/`.

**Reviewer:** statements match Bala's text?  ☐ yes  ☐ no  — notes:
