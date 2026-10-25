/-
Parts of this file are taken from the benchmark file statements/lean-targets/333561_b286c526.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A333561Main

open Nat Finset

/-- We conjecture that this sequence satisfies the supercongruences
a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k.
-/
theorem oeis_333561_conjecture :
  ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((3 : ℕ) : ℤ) (-1) 2 a
    (fun N hN => by rw [TF.A_m_neg_one 3 2 N hN]; rfl) hn hk
  exact_mod_cast h
