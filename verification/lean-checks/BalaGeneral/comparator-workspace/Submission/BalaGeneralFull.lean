import Submission.TFMain
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Two general conjectures of Peter Bala (OEIS A352373 and A333715), for primes `p ≥ 5`

* OEIS A352373, comments: "let r and s be integers and define a sequence (a(r,s;n))n>=1 by
  a(r,s;n) = [x^n] ( (1 + x)^r * (1 - x)^s )^n. Conjecture: for each r and s the above
  supercongruences hold for the sequence a(r,s;n) for n >= 1", the supercongruences being
  a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for all primes p >= 5 and positive integers n and k.
* OEIS A333715, comments: "The same congruences may hold more generally for the sequences
  a(r,s,n) := [x^(r*n)]( (1 + x)/(1 - x) )^(s*n), r a positive integer and s an integer."

For an integer `t`, `(1 + x)^t` is Mathlib's `PowerSeries.binomialSeries ℤ t` (coefficients
`Ring.choose t k`) and `(1 - x)^t` is obtained from it by `x ↦ -x` (`PowerSeries.rescale (-1)`).
Both conjectures are instances of Theorem F (`TF.theoremF`): `a(r,s;n) = A(r,s,1;n)` and
`a(r,s,n) = A(s,-s,r;n)`, where `A(a,b,c;N) = [x^{cN}] ((1+x)^a (1-x)^b)^N`.
-/

namespace BalaGeneral

open PowerSeries Epoch333042.Super TF

noncomputable section

/-- `[x^m] ((1 + x)^a (1 - x)^b)^N` for integers `a`, `b`. -/
def coeffPow (a b : ℤ) (m N : ℕ) : ℤ :=
  coeff m ((binomialSeries ℤ a * rescale (-1) (binomialSeries ℤ b)) ^ N)

/-- Bala's `a(r,s;n) = [x^n] ((1 + x)^r (1 - x)^s)^n` (OEIS A352373). -/
def aRS (r s : ℤ) (n : ℕ) : ℤ :=
  coeff n ((binomialSeries ℤ r * rescale (-1) (binomialSeries ℤ s)) ^ n)

/-- Bala's `a(r,s,n) = [x^(r n)] ((1 + x)/(1 - x))^(s n) = [x^(r n)] ((1 + x)^s (1 - x)^(-s))^n`
(OEIS A333715). -/
def aRSn (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) ((binomialSeries ℤ s * rescale (-1) (binomialSeries ℤ (-s))) ^ n)

theorem binomialSeries_mul_neg (t : ℤ) :
    binomialSeries ℚ t * binomialSeries ℚ (-t) = 1 := by
  have h := binomialSeries_add (A := ℚ) t (-t)
  rw [add_neg_cancel, binomialSeries_zero] at h
  exact h.symm

/-- `exp(t log(1+x)) = (1+x)^t` for every integer `t`. -/
theorem expS_zsmul_lp (t : ℤ) : expS ((t : ℚ) • TF.lp) = binomialSeries ℚ t := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · rw [Int.cast_natCast, Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_lp, binomialSeries_nat]
  · have h1 : expS ((n : ℚ) • TF.lp) * expS (((-(n : ℤ) : ℤ) : ℚ) • TF.lp) = 1 := by
      rw [Int.cast_neg, Int.cast_natCast, neg_smul]; exact expS_mul_expS_neg _
    have h2 : expS ((n : ℚ) • TF.lp) * binomialSeries ℚ (-(n : ℤ)) = 1 := by
      rw [Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_lp, ← binomialSeries_nat (R := ℤ)]
      exact binomialSeries_mul_neg n
    exact TF.inv_unique h1 h2

/-- `exp(t log(1-x)) = (1-x)^t` for every integer `t`. -/
theorem expS_zsmul_lm (t : ℤ) : expS ((t : ℚ) • lm) = rescale (-1) (binomialSeries ℚ t) := by
  have hX : rescale (-1 : ℚ) (1 + X) = 1 - X := by
    rw [map_add, map_one, rescale_neg_one_X, sub_eq_add_neg]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · rw [Int.cast_natCast, Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_lm, binomialSeries_nat,
      map_pow, hX]
  · have h1 : expS ((n : ℚ) • lm) * expS (((-(n : ℤ) : ℤ) : ℚ) • lm) = 1 := by
      rw [Int.cast_neg, Int.cast_natCast, neg_smul]; exact expS_mul_expS_neg _
    have h2 : expS ((n : ℚ) • lm) * rescale (-1) (binomialSeries ℚ (-(n : ℤ))) = 1 := by
      rw [Nat.cast_smul_eq_nsmul ℚ, expS_nsmul, expS_lm, ← hX, ← map_pow,
        ← binomialSeries_nat (R := ℤ), ← map_mul, binomialSeries_mul_neg, map_one]
    exact TF.inv_unique h1 h2

theorem map_binomialSeries (t : ℤ) :
    map (Int.castRingHom ℚ) (binomialSeries ℤ t) = binomialSeries ℚ t := by
  ext n
  simp [coeff_map, binomialSeries_coeff]

theorem map_rescale_neg_one (f : ℤ⟦X⟧) :
    map (Int.castRingHom ℚ) (rescale (-1) f) = rescale (-1) (map (Int.castRingHom ℚ) f) := by
  ext n
  simp [coeff_map, coeff_rescale]

/-- `φ = exp(a log(1+x) + b log(1-x)) = (1+x)^a (1-x)^b` for all integers `a`, `b`. -/
theorem expS_F (a b : ℤ) :
    expS (F a b) = binomialSeries ℚ a * rescale (-1) (binomialSeries ℚ b) := by
  rw [F_eq, expS_add, expS_zsmul_lp, expS_zsmul_lm]

/-- The coefficients of `((1+x)^a (1-x)^b)^N` are the `A a b c N` of Theorem F. -/
theorem coeffPow_eq_A (a b : ℤ) (c N : ℕ) : (coeffPow a b (c * N) N : ℚ) = A a b c N := by
  have hm : map (Int.castRingHom ℚ) ((binomialSeries ℤ a * rescale (-1) (binomialSeries ℤ b)) ^ N)
      = Phi a b N := by
    rw [Phi_eq_pow, expS_F, map_pow, map_mul, map_binomialSeries, map_rescale_neg_one,
      map_binomialSeries]
  rw [A, ← hm, coeff_map, coeffPow]
  rfl

/-- Theorem F as a divisibility statement for an integer-valued sequence. -/
theorem tower_int' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℤ) (c : ℕ) (s : ℕ → ℤ)
    (hs : ∀ N, 1 ≤ N → (s N : ℚ) = A a b c N) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (p : ℤ) ^ (3 * k) ∣ s (n * p ^ k) - s (n * p ^ (k - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hM0 : n * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero)
  have hM1 : n * p ^ (j + 1) ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero)
  have hpM : n * p ^ (j + 1) = p * (n * p ^ j) := by ring
  have hF := theoremF (p := p) hp5 a b c (n * p ^ j)
  have hv : j ≤ padicValNat p (n * p ^ j) :=
    (padicValNat_dvd_iff_le hM0).mp (dvd_mul_left (p ^ j) n)
  have hV : V p ((3 * (j + 1) : ℕ) : ℤ) ((s (n * p ^ (j + 1)) : ℚ) - (s (n * p ^ j) : ℚ)) := by
    rw [hs _ (Nat.one_le_iff_ne_zero.mpr hM1), hs _ (Nat.one_le_iff_ne_zero.mpr hM0), hpM]
    exact V_mono hF (by omega)
  exact (V_int_iff_dvd (p := p) (3 * (j + 1)) (s (n * p ^ (j + 1)) - s (n * p ^ j))).mp
    (by rw [Int.cast_sub]; exact hV)

theorem modEq_of_tower {p n k : ℕ} {u : ℕ → ℤ}
    (h : (p : ℤ) ^ (3 * k) ∣ u (n * p ^ k) - u (n * p ^ (k - 1))) :
    u (n * p ^ k) ≡ u (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] :=
  (Int.modEq_iff_dvd.mpr h).symm

/-- **Bala's general conjecture on OEIS A352373**, for primes `p ≥ 5`: for all integers `r`, `s`,
`a(r,s;n p^k) ≡ a(r,s;n p^(k-1)) (mod p^(3k))` for all `n, k ≥ 1`. -/
theorem full_A352373_general (r s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRS r s (n * p ^ k) ≡ aRS r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  apply modEq_of_tower
  refine tower_int' hp hp5 r s 1 (aRS r s) (fun N _ => ?_) hn hk
  have h := coeffPow_eq_A r s 1 N
  rw [one_mul] at h
  exact h

/-- **Bala's general conjecture on OEIS A333715**, for primes `p ≥ 5`: for every `r ≥ 0` and every
integer `s`, `a(r,s,n p^k) ≡ a(r,s,n p^(k-1)) (mod p^(3k))` for all `n, k ≥ 1`
(Bala states it for `r ≥ 1`). -/
theorem full_A333715_general (r : ℕ) (s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRSn r s (n * p ^ k) ≡ aRSn r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  apply modEq_of_tower
  exact tower_int' hp hp5 s (-s) r (aRSn r s) (fun N _ => coeffPow_eq_A s (-s) r N) hn hk

end

end BalaGeneral
