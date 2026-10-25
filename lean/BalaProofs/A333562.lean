/-
Parts of this file are taken from the benchmark file statements/lean-targets/333562_2eccaf4c.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A333562Main

open Nat Finset

/--
We conjecture that this sequence satisfies the congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((4 : ℕ) : ℤ) (-1) 3 a
    (fun N hN => by rw [TF.A_m_neg_one 4 3 N hN, A333562.a_eq_rep N hN]) hn hk
  exact_mod_cast h
