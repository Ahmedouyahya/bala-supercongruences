/-
Parts of this file are taken from the benchmark file statements/lean-targets/376462_96154f2f.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A376462Main

open Nat Finset

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
    ) := by
  intro p n r hp hp5 hn hr
  exact ⟨A376462_first p n r hp hp5 hn hr, A376462_shifted p n r hp hp5 hn hr⟩
