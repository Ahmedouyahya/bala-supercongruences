import Mathlib

open Finset

/-- Core arithmetic fact behind Lemma 3 of A361711 (`notes/A361711-proof.md`): for a prime `p ≥ 5`,
`k ≥ 1` and any integer `S` with `6 S = (q−1) q (2q−1) − p² (m−1) m (2m−1)`, where `q = p^k`, `m = p^(k−1)`,
one has `p^k ∣ S` (the two products carry `p^k` and `p^(k+1)` respectively, and `6` is a unit mod `p`). -/
theorem pk_dvd_core (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (S : ℤ)
    (hS : 6 * S = ((p:ℤ) ^ k - 1) * (p:ℤ) ^ k * (2 * (p:ℤ) ^ k - 1)
                  - (p:ℤ) ^ 2 * (((p:ℤ) ^ (k - 1) - 1) * (p:ℤ) ^ (k - 1) * (2 * (p:ℤ) ^ (k - 1) - 1))) :
    (p:ℤ) ^ k ∣ S := by
  -- 6 and p^k are coprime
  have hnd : ¬ p ∣ 6 := by
    intro h
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · exact absurd h (by norm_num)
    · exact absurd hp (by norm_num)
  have hcop6 : Nat.Coprime 6 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  have h6 : IsCoprime (6 : ℤ) ((p:ℤ) ^ k) := by
    have h := (Nat.isCoprime_iff_coprime.mpr hcop6)
    exact_mod_cast h.pow_right
  -- p^k divides 6 S
  have hA : (p:ℤ) ^ k ∣ ((p:ℤ) ^ k - 1) * (p:ℤ) ^ k * (2 * (p:ℤ) ^ k - 1) :=
    Dvd.dvd.mul_right (dvd_mul_left _ _) _
  have hB : (p:ℤ) ^ k ∣ (p:ℤ) ^ 2 * (((p:ℤ) ^ (k - 1) - 1) * (p:ℤ) ^ (k - 1) * (2 * (p:ℤ) ^ (k - 1) - 1)) := by
    have hpow : (p:ℤ) ^ k ∣ (p:ℤ) ^ 2 * (p:ℤ) ^ (k - 1) := by
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    have hre : (p:ℤ) ^ 2 * (((p:ℤ) ^ (k - 1) - 1) * (p:ℤ) ^ (k - 1) * (2 * (p:ℤ) ^ (k - 1) - 1))
        = ((p:ℤ) ^ 2 * (p:ℤ) ^ (k - 1)) * (((p:ℤ) ^ (k - 1) - 1) * (2 * (p:ℤ) ^ (k - 1) - 1)) := by ring
    rw [hre]
    exact Dvd.dvd.mul_right hpow _
  have hdvd : (p:ℤ) ^ k ∣ 6 * S := by
    rw [hS]
    exact dvd_sub hA hB
  exact h6.symm.dvd_of_dvd_mul_left hdvd
