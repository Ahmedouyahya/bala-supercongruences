import BalaCheck.EpochSol
import FormalConjectures.OEIS.Auto.«352275_4b1f2230»

/-!
# Bala's conjecture on A352275, for every `u_m`

The statement is taken from the Formal Conjectures file `FormalConjectures/OEIS/Auto/352275_4b1f2230.lean`
(branch `auto_oeis`, commit 67338a1), imported unchanged: the final theorem is stated as
`type_of% @u_m_supercongruence_conjecture`.

Proof: for `n ≥ 1` each term `n/(n+2k) · C(n+2k,k)` of `u m n` is the non-negative integer
`C(n+2k-1,k) - C(n+2k-1,k-1) = formalCatalanCoeff n k`, so `u m n = formalPartial n (m n) = FNat ((2m+1) n) (m n)`
(`formalPartial_eq_FNat`), and `FNat_scale_supercongruence` (both from the accepted Lean proof of A333096 in the
OEIS Open evaluation, run oeis-lite-200usd-sol-nk5wh4g0vh3546nm) gives the congruence modulo `p^(3r)`.
-/

open Nat Finset BigOperators

namespace BalaA352275

/-- `C(n+2k-1, k) · (n+2k) = C(n+2k, k) · (n+k)`. -/
lemma choose_id1 (n k : ℕ) (hn : 0 < n) :
    (n + 2 * k - 1).choose k * (n + 2 * k) = (n + 2 * k).choose k * (n + k) := by
  have h := Nat.choose_mul_succ_eq (n + 2 * k - 1) k
  have e1 : n + 2 * k - 1 + 1 = n + 2 * k := by omega
  rw [e1] at h
  have e2 : n + 2 * k - k = n + k := by omega
  rw [e2] at h
  exact h

/-- `C(n+2k-1, k-1) · (n+2k) = C(n+2k, k) · k` for `k ≥ 1`. -/
lemma choose_id2 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (n + 2 * k - 1).choose (k - 1) * (n + 2 * k) = (n + 2 * k).choose k * k := by
  have h := Nat.add_one_mul_choose_eq (n + 2 * k - 1) (k - 1)
  have e1 : n + 2 * k - 1 + 1 = n + 2 * k := by omega
  have e2 : k - 1 + 1 = k := by omega
  rw [e1, e2] at h
  calc (n + 2 * k - 1).choose (k - 1) * (n + 2 * k)
      = (n + 2 * k) * (n + 2 * k - 1).choose (k - 1) := Nat.mul_comm _ _
    _ = (n + 2 * k).choose k * k := h

/-- For `n, k ≥ 1`, `formalCatalanCoeff n k = C(n+2k-1, k) - C(n+2k-1, k-1)`. -/
lemma fcc_nat (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    formalCatalanCoeff (n : ℤ) k
      = (((n + 2 * k - 1).choose k : ℕ) : ℤ) - (((n + 2 * k - 1).choose (k - 1) : ℕ) : ℤ) := by
  have hcast : ((n + 2 * k - 1 : ℕ) : ℤ) = (n : ℤ) + 2 * (k : ℤ) - 1 := by
    have : 1 ≤ n + 2 * k := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [formalCatalanCoeff, if_neg (Nat.pos_iff_ne_zero.mp hk), ← hcast, Ring.choose_natCast,
    Ring.choose_natCast]

/-- The rational term of `u` equals `formalCatalanCoeff n k`. -/
lemma term_eq (n k : ℕ) (hn : 0 < n) :
    ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))
      = ((formalCatalanCoeff (n : ℤ) k : ℤ) : ℚ) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [formalCatalanCoeff, hnq.ne']
  · rw [fcc_nat n k hn hk]
    have h1q : (((n + 2 * k - 1).choose k : ℕ) : ℚ) * ((n : ℚ) + 2 * (k : ℚ))
        = (((n + 2 * k).choose k : ℕ) : ℚ) * ((n : ℚ) + (k : ℚ)) := by
      exact_mod_cast choose_id1 n k hn
    have h2q : (((n + 2 * k - 1).choose (k - 1) : ℕ) : ℚ) * ((n : ℚ) + 2 * (k : ℚ))
        = (((n + 2 * k).choose k : ℕ) : ℚ) * (k : ℚ) := by
      exact_mod_cast choose_id2 n k hn hk
    have hpos : (0 : ℚ) < (n : ℚ) + 2 * (k : ℚ) := by positivity
    push_cast
    rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']
    linear_combination h2q - h1q

/-- Each summand of `u m n` (for `n ≥ 1`), after `Rat.floor` and `Int.toNat`, is `formalCatalanCoeff n k`. -/
lemma term_toNat (n k : ℕ) (hn : 0 < n) :
    (((Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))).toNat : ℕ) : ℤ)
      = formalCatalanCoeff (n : ℤ) k := by
  have hnn : 0 ≤ formalCatalanCoeff (n : ℤ) k := by
    have h0 : (0 : ℚ) ≤ (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ) := by positivity
    rw [term_eq n k hn] at h0
    exact_mod_cast h0
  rw [term_eq n k hn]
  have hfloor : Rat.floor ((formalCatalanCoeff (n : ℤ) k : ℤ) : ℚ) = formalCatalanCoeff (n : ℤ) k :=
    Int.floor_intCast (R := ℚ) (formalCatalanCoeff (n : ℤ) k)
  rw [hfloor]
  exact Int.toNat_of_nonneg hnn

/-- `u m n = formalPartial n (m n)` for `n ≥ 1`. -/
lemma u_eq_formalPartial (m n : ℕ) (hn : 0 < n) :
    (u m n : ℤ) = formalPartial (n : ℤ) (m * n) := by
  rw [u, if_neg (Nat.pos_iff_ne_zero.mp hn)]
  push_cast
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k _
  exact term_toNat n k hn

/-- `u m n = FNat ((2m+1) n) (m n)` for `n ≥ 1`. -/
lemma u_eq_FNat (m n : ℕ) (hn : 0 < n) :
    (u m n : ℤ) = FNat ((2 * m + 1) * n) (m * n) := by
  rw [u_eq_formalPartial m n hn, ← formalPartial_eq_FNat ((2 * m + 1) * n) (m * n)]
  congr 1
  push_cast
  ring

/-- The supercongruence for every `u_m` (the hypothesis `m > 0` of the target is not needed). -/
theorem u_scale (m n r : ℕ) (hn : 0 < n) (hr : 0 < r) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD ((p : ℤ) ^ (3 * r))] := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hN : 0 < n * p ^ s := Nat.mul_pos hn (pow_pos hp.pos s)
  have hpN : n * p ^ (s + 1) = p * (n * p ^ s) := by ring
  rw [Nat.add_sub_cancel, hpN, u_eq_FNat m (p * (n * p ^ s)) (Nat.mul_pos hp.pos hN),
    u_eq_FNat m (n * p ^ s) hN]
  have hB : p ^ s ∣ m * (n * p ^ s) := (dvd_mul_left (p ^ s) n).mul_left m
  have hY : p ^ s ∣ (m + 1) * (n * p ^ s) := (dvd_mul_left (p ^ s) n).mul_left (m + 1)
  have h := FNat_scale_supercongruence (lev := s) hp hp5 hB hY
  convert h using 2 <;> ring

end BalaA352275

/-- Bala's conjecture on A352275 for every `u_m`, with the statement taken from the target file. -/
theorem A352275_from_target : type_of% @u_m_supercongruence_conjecture := by
  intro m n r _hm hn hr p hp hp5
  exact BalaA352275.u_scale m n r hn hr p hp hp5

/-- Sanity: A352275 is `u_2`. -/
theorem A352275_a_eq_u2 : a = u 2 := rfl
