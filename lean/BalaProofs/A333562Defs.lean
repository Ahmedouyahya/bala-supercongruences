/-
Parts of this file are taken from the benchmark file statements/lean-targets/333562_2eccaf4c.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions are copied verbatim from that file; the import lines differ.
-/
import Mathlib

open Nat Finset

/--
A333562: $a(n) = \sum_{j = 0}^{3n} \binom{n+j-1}{j} 2^j$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (3 * n + 1)) fun j =>
    (n + j - 1).choose j * (2 ^ j)
