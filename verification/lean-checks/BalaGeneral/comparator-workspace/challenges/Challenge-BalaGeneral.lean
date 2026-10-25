import Mathlib

open PowerSeries

namespace BalaGeneral

/-- Bala, OEIS A352373: `a(r,s;n) = [x^n] ((1 + x)^r (1 - x)^s)^n`. -/
noncomputable def aRS (r s : ℤ) (n : ℕ) : ℤ :=
  coeff n ((binomialSeries ℤ r * rescale (-1) (binomialSeries ℤ s)) ^ n)

/-- Bala, OEIS A333715: `a(r,s,n) = [x^(r n)] ((1 + x)/(1 - x))^(s n)`. -/
noncomputable def aRSn (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) ((binomialSeries ℤ s * rescale (-1) (binomialSeries ℤ (-s))) ^ n)

theorem bala_A352373_general (r s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRS r s (n * p ^ k) ≡ aRS r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

theorem bala_A333715_general (r : ℕ) (s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    aRSn r s (n * p ^ k) ≡ aRSn r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end BalaGeneral
