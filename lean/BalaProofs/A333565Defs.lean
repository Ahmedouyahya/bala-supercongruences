/-
Parts of this file are taken from the benchmark file statements/lean-targets/333565_757e3efd.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions are copied verbatim from that file; the import lines differ.
-/
import Mathlib

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
