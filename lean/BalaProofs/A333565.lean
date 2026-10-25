/-
Parts of this file are taken from the benchmark file statements/lean-targets/333565_757e3efd.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the statement is copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import BalaProofs.A333565Main

open Nat Int BigOperators

/--
We conjecture that this sequence satisfies the stronger congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 3$ and positive integers $n$ and $k$.
-/
theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] := by
  have hB : ∀ N, 1 ≤ N → ((A333565.B N : ℕ) : ℚ) = TF.A 2 (-1) 1 N := by
    intro N hN
    have h := TF.A_m_neg_one 2 1 N hN
    rw [Nat.cast_ofNat] at h
    rw [h, A333565.B_eq_coeffForm N hN]
    simp only [one_mul]
  have hdiv : (p : ℤ) ^ (3 * k)
      ∣ (A333565.B (n * p ^ k) : ℤ) - (A333565.B (n * p ^ (k - 1)) : ℤ) := by
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · obtain rfl : p = 3 := by
        interval_cases p
        · rfl
        · exact absurd hp (by norm_num)
      exact_mod_cast TF.tower_three A333565.B hB hn hk
    · exact TF.tower_int hp h5 2 (-1) 1 A333565.B hB hn hk
  have hodd : ¬ Even p := by
    rw [hp.even_iff]
    omega
  have hpar : Even (n * p ^ k) ↔ Even (n * p ^ (k - 1)) := by
    simp [Nat.even_mul, Nat.even_pow, hodd]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd, A333565.A333565_diff _ _ hpar]
  exact Dvd.dvd.mul_left hdiv 2
