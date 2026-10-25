/-
Parts of this file are taken from the benchmark file statements/lean-targets/370092_862cfcda.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A370092Main

open Finset Nat

/--
%C A370092 Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).
-/
theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  refine ⟨Nat.totient k, dvd_refl _, ?_⟩
  unfold eventually_periodic
  refine ⟨k + 2, fun n hn => ?_⟩
  unfold a_mod_k
  rw [A370092.a_num, A370092.a_num]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (A370092.k_dvd k hk n hn))
