/-
Parts of this file are taken from the benchmark file statements/lean-targets/352373_a1d5fa75.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A352373Main

open scoped BigOperators Nat Finset Int

/--
A352373 Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
hold for all primes p >= 5 and positive integers n and k.
-/
theorem oeis_a352373_supercongruence :
  ∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),
  ∀ (n : ℕ) (hn_pos : 0 < n),
  ∀ (k : ℕ) (hk_pos : 0 < k),
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  intro p hp hp5 n hn k hk
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
  exact TF.tower_int hp hp5 (-1) (-3) 1 a
    (fun N hN => by
      rw [TF.A_neg_one_neg_three N hN]
      simp only [a, if_neg (show N ≠ 0 by omega)]) hn hk
