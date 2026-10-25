/-
Parts of this file are taken from the benchmark file statements/lean-targets/386548_8788c4f8.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions are copied verbatim from that file; the import lines differ.
-/
/-
Definition of A386548 copied verbatim from statements/lean-targets/386548_8788c4f8.lean (lines from `open` to the end of `def a`);
only the import line differs.
-/
import Mathlib

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
