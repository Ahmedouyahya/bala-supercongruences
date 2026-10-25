/-
Parts of this file are taken from the benchmark file statements/lean-targets/363983_3f7e4c53.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A363983Main

open Nat Finset Int

/-- oeis_363983_conjecture_0: The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences. -/
theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  have hN : 1 ≤ n * p ^ r :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hM : 1 ≤ n * p ^ (r - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  rw [A363983.cast_A363983 _ hN, A363983.cast_A363983 _ hM]
  exact (Int.modEq_iff_dvd.mpr (A363983.s_cong p hp h_p_ge_5 n r hn hr)).symm
