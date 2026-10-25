/-
Parts of this file are taken from the benchmark file statements/lean-targets/376462_96154f2f.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions are copied verbatim from that file; the import lines differ.
-/
import Mathlib

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
