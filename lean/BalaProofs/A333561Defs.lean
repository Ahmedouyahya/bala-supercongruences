/-
Parts of this file are taken from the benchmark file statements/lean-targets/333561_b286c526.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions are copied verbatim from that file; the import lines differ.
-/
import Mathlib

open Nat Finset

/--
A333561: $a(n) = \sum_{k = 0}^{2n} \binom{3n}{2n-k}\binom{n+k-1}{k}$.
This is an equivalent identity conjectured in the OEIS entry, which may resolve issues with the automated checker.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (2 * n + 1)) fun k : ℕ =>
    Nat.choose (3 * n) (2 * n - k) * Nat.choose (n + k - 1) k
