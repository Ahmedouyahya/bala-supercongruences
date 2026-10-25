/-
Parts of this file are taken from the benchmark file statements/lean-targets/386548_8788c4f8.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A386548Main

open Finset Nat BigOperators Int

/--
Conjecture: the stronger supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{2k}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $k$.
-/
theorem oeis_A386548_supercongruence_conjecture :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k) : ℤ)] :=
by
  intro p hp hp5 n k hn hk
  set M := n * p ^ (k - 1) with hMdef
  have hM : 1 ≤ M :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hN : n * p ^ k = p * M := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hMdef, Nat.add_sub_cancel, pow_succ]; ring
  have hdiv := A386548.S_cong p hp hp5 M k hM hk (dvd_mul_left _ _)
  have h1 : a (n * p ^ k) = A386548.S (p * M) := by
    rw [hN]; exact A386548.a_eq_S _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega)))
  rw [h1, A386548.a_eq_S M hM]
  exact (Int.modEq_iff_dvd.mpr hdiv).symm
