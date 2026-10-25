import FormalConjectures.OEIS.Auto.«363983_3f7e4c53»

/-!
# A363983, part 1: the defining integer sum is positive

`A363983 n` is defined in the Formal Conjectures file as `(Σ_{k ≤ n} T n k).toNat` with
`T n k = (-1)^(n+k) C(n,k) C(n+k-1,k) C(2k,n)` (`(n + k).pred` for `n + k - 1`).  We prove
`0 < Σ_{k ≤ n} T n k` for `n ≥ 1`, hence `(A363983 n : ℤ) = Σ_{k ≤ n} T n k` (`cast_A363983`).

Route: Zeilberger certificate (Maxima, checked in `lean-check/A363983/cert_check.py`),
`dd(n) (c0 F(n,k) + c1 F(n+1,k) + c2 F(n+2,k)) = G(n,k+1) - G(n,k)`, verified as a polynomial
identity after writing every term as `(-1)^(n+k) C(n+3,k+1) C(n+k+1,k+1) C(2k+4,n+2)` times a
polynomial (relations `r1*`, `r2*`, `r3*`); telescoping gives the 3-term recurrence `rec_s`;
then `s(n+1) ≥ 7 s(n) > 0` by induction (`s_pos`).
-/

open Finset

namespace A363983

/-- The summand of the target's definition. -/
def T (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n + k) * ((n.choose k : ℤ) * ((n + k).pred.choose k : ℤ) * ((2 * k).choose n : ℤ))

/-- The integer sum defining `A363983`. -/
def s (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), T n k

lemma A363983_eq_toNat (n : ℕ) : _root_.A363983 n = (s n).toNat := rfl

lemma s_one : s 1 = 2 := by decide

lemma s_two : s 2 = 14 := by decide

/- ### The certificate data (rational functions in `n`, `k`) -/

/-- the certificate numerator `P(n,k)` -/
def P (n k : ℚ) : ℚ :=
  50*k*n^5 - 35*n^5 - 10*k^2*n^4 + 275*k*n^4 - 209*n^4 - 48*k^2*n^3 + 589*k*n^3 - 470*n^3
    - 74*k^2*n^2 + 596*k*n^2 - 488*n^2 - 40*k^2*n + 272*k*n - 228*n - 8*k^2 + 48*k - 40

/-- recurrence coefficients -/
def c0 (n : ℚ) : ℚ := 3*n*(3*n+1)*(3*n+2)*(5*n^2+14*n+10)
def c1 (n : ℚ) : ℚ := -((n+1)*(145*n^4+551*n^3+694*n^2+324*n+56))
def c2 (n : ℚ) : ℚ := 2*(n+1)*(n+2)^2*(5*n^2+4*n+1)

/-- common denominator of the certificate -/
def dd (n : ℚ) : ℚ := n*(n+1)^2*(n+2)

/-- the telescoping term `G(n,k) = dd(n) R(n,k) F(n,k)`, with the pole of `R` cancelled
against `C(n,k)` (`C(n,k)/((n-k+1)(n-k+2)) = C(n+2,k)/((n+1)(n+2))`). -/
def G (n k : ℕ) : ℚ :=
  (-(k : ℚ) * ((n : ℚ) - 2 * k) * ((n : ℚ) - 2 * k + 1) * P n k)
    * ((-1 : ℚ) ^ (n + k) * ((((n + 2).choose k : ℕ) : ℚ) * (((n + k - 1).choose k : ℕ) : ℚ)
      * (((2 * k).choose n : ℕ) : ℚ)))

/- ### Binomial identities in `ℚ` (no side conditions) -/

lemma q_mul_succ (N j : ℕ) :
    (((N + 1).choose j : ℕ) : ℚ) * ((N : ℚ) + 1 - j) = ((N.choose j : ℕ) : ℚ) * ((N : ℚ) + 1) := by
  rcases le_or_gt j (N + 1) with h | h
  · have h1 := Nat.choose_mul_succ_eq N j
    have h2 : ((N + 1 - j : ℕ) : ℚ) = (N : ℚ) + 1 - j := by rw [Nat.cast_sub h]; push_cast; ring
    rw [← h2]; exact_mod_cast h1.symm
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : N < j)]; simp

lemma q_succ_right (N j : ℕ) :
    ((N.choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) = ((N.choose j : ℕ) : ℚ) * ((N : ℚ) - j) := by
  rcases le_or_gt j N with h | h
  · have h1 := Nat.choose_succ_right_eq N j
    have h2 : ((N - j : ℕ) : ℚ) = (N : ℚ) - j := by rw [Nat.cast_sub h]
    rw [← h2]; exact_mod_cast h1
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : N < j + 1)]; simp

lemma q_succ_mul (N j : ℕ) :
    ((N : ℚ) + 1) * ((N.choose j : ℕ) : ℚ) = (((N + 1).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) := by
  exact_mod_cast Nat.add_one_mul_choose_eq N j

/- ### Every binomial as a polynomial multiple of the base binomials
`b1 = C(n+3,k+1)`, `b2 = C(n+k+1,k+1)`, `b3 = C(2k+4,n+2)` -/

section rel

variable (n k : ℕ)

lemma m1c : (((n + 2).choose k : ℕ) : ℚ) * ((n : ℚ) + 3)
    = (((n + 3).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) := by
  have h := q_succ_mul (n + 2) k
  rw [show n + 2 + 1 = n + 3 by ring] at h
  push_cast at h
  linear_combination h

lemma m1d : (((n + 2).choose (k + 1) : ℕ) : ℚ) * ((n : ℚ) + 3)
    = (((n + 3).choose (k + 1) : ℕ) : ℚ) * ((n : ℚ) + 2 - k) := by
  have h := q_mul_succ (n + 2) (k + 1)
  rw [show n + 2 + 1 = n + 3 by ring] at h
  push_cast at h
  linear_combination -h

lemma m1b : (((n + 1).choose k : ℕ) : ℚ) * (((n : ℚ) + 2) * ((n : ℚ) + 3))
    = (((n + 3).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * ((n : ℚ) + 2 - k)) := by
  have hA := q_mul_succ (n + 1) k
  rw [show n + 1 + 1 = n + 2 by ring] at hA
  push_cast at hA
  have hB := m1c n k
  linear_combination (-((n : ℚ) + 3)) * hA + ((n : ℚ) + 2 - k) * hB

lemma m1a : ((n.choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3))
    = (((n + 3).choose (k + 1) : ℕ) : ℚ)
      * (((k : ℚ) + 1) * ((n : ℚ) + 2 - k) * ((n : ℚ) + 1 - k)) := by
  have hA := q_mul_succ n k
  have hB := m1b n k
  linear_combination (-(((n : ℚ) + 2) * ((n : ℚ) + 3))) * hA + ((n : ℚ) + 1 - k) * hB

lemma m2b : (((n + k).choose k : ℕ) : ℚ) * ((n : ℚ) + k + 1)
    = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) := by
  have h := q_succ_mul (n + k) k
  push_cast at h
  linear_combination h

lemma m2c : (((n + k + 1).choose k : ℕ) : ℚ) * ((n : ℚ) + 1)
    = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) := by
  have h := q_succ_right (n + k + 1) k
  push_cast at h
  linear_combination -h

lemma m2d : (((n + k).choose (k + 1) : ℕ) : ℚ) * ((n : ℚ) + k + 1)
    = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * (n : ℚ) := by
  have h := q_mul_succ (n + k) (k + 1)
  push_cast at h
  linear_combination -h

lemma m2a (hn : 1 ≤ n) : (((n + k - 1).choose k : ℕ) : ℚ) * (((n : ℚ) + k) * ((n : ℚ) + k + 1))
    = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * (n : ℚ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA := q_mul_succ (m + k) k
  rw [show m + k + 1 = m + 1 + k by ring] at hA
  rw [show m + 1 + k - 1 = m + k by omega]
  push_cast at hA ⊢
  have hB := m2b (m + 1) k
  push_cast at hB
  linear_combination (-((m : ℚ) + 1 + k + 1)) * hA + ((m : ℚ) + 1) * hB

lemma m3d : (((2 * k + 2).choose n : ℕ) : ℚ) * ((2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))
    = (((2 * k + 4).choose (n + 2) : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
  have hA := q_succ_mul (2 * k + 2) n
  have hB := q_succ_mul (2 * k + 3) (n + 1)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 by ring] at hA
  rw [show 2 * k + 3 + 1 = 2 * k + 4 by ring, show n + 1 + 1 = n + 2 by ring] at hB
  push_cast at hA hB
  linear_combination (2 * (k : ℚ) + 4) * hA + ((n : ℚ) + 1) * hB

lemma m3a : (((2 * k).choose n : ℕ) : ℚ)
      * ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))
    = (((2 * k + 4).choose (n + 2) : ℕ) : ℚ)
      * (((n : ℚ) + 1) * ((n : ℚ) + 2) * (2 * (k : ℚ) + 2 - n) * (2 * (k : ℚ) + 1 - n)) := by
  have hA := q_mul_succ (2 * k) n
  have hB := q_mul_succ (2 * k + 1) n
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hB
  push_cast at hA hB
  have hC := m3d n k
  linear_combination (-((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))) * hA
    + (-((2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4) * (2 * (k : ℚ) + 1 - n))) * hB
    + ((2 * (k : ℚ) + 1 - n) * (2 * (k : ℚ) + 2 - n)) * hC

lemma m3b : (((2 * k).choose (n + 1) : ℕ) : ℚ)
      * ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))
    = (((2 * k + 4).choose (n + 2) : ℕ) : ℚ)
      * (((n : ℚ) + 2) * (2 * (k : ℚ) + 2 - n) * (2 * (k : ℚ) + 1 - n) * (2 * (k : ℚ) - n)) := by
  have h := q_succ_right (2 * k) n
  push_cast at h
  have ha := m3a n k
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  linear_combination ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3)
    * (2 * (k : ℚ) + 4)) * h + (2 * (k : ℚ) - n) * ha

lemma m3c : (((2 * k).choose (n + 2) : ℕ) : ℚ)
      * ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))
    = (((2 * k + 4).choose (n + 2) : ℕ) : ℚ)
      * ((2 * (k : ℚ) + 2 - n) * (2 * (k : ℚ) + 1 - n) * (2 * (k : ℚ) - n)
        * (2 * (k : ℚ) - n - 1)) := by
  have h := q_succ_right (2 * k) (n + 1)
  rw [show n + 1 + 1 = n + 2 by ring] at h
  push_cast at h
  have hb := m3b n k
  have hne : ((n : ℚ) + 2) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  linear_combination ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3)
    * (2 * (k : ℚ) + 4)) * h + (2 * (k : ℚ) - n - 1) * hb

end rel

/-- product of three relations -/
lemma tri (σ X Y Z D1 D2 D3 b1 b2 b3 q1 q2 q3 : ℚ) (h1 : X * D1 = b1 * q1)
    (h2 : Y * D2 = b2 * q2) (h3 : Z * D3 = b3 * q3) :
    σ * (X * Y * Z) * (D1 * D2 * D3) = σ * (b1 * b2 * b3) * (q1 * q2 * q3) := by
  linear_combination (σ * (Y * D2) * (Z * D3)) * h1 + (σ * b1 * q1 * (Z * D3)) * h2
    + (σ * b1 * q1 * b2 * q2) * h3

/- ### The certificate identity -/

lemma T_cast (n k : ℕ) : ((T n k : ℤ) : ℚ) = (-1 : ℚ) ^ (n + k)
    * (((n.choose k : ℕ) : ℚ) * (((n + k - 1).choose k : ℕ) : ℚ) * (((2 * k).choose n : ℕ) : ℚ)) := by
  simp only [T, Nat.pred_eq_sub_one]
  push_cast
  ring

/-- The certificate identity reduced to a polynomial identity (checked by `ring`). -/
lemma poly_id (x y : ℚ) :
    dd x * (c0 x * (((y + 1) * (x + 2 - y) * (x + 1 - y)) * ((y + 1) * x * (x + 1))
          * ((x + 1) * (x + 2) * (2 * y + 2 - x) * (2 * y + 1 - x)))
        - c1 x * (((y + 1) * (x + 2 - y) * (x + 1)) * ((y + 1) * (x + 1) * (x + y))
          * ((x + 2) * (2 * y + 2 - x) * (2 * y + 1 - x) * (2 * y - x)))
        + c2 x * (((y + 1) * (x + 1) * (x + 2)) * ((y + 1) * (x + y) * (x + y + 1))
          * ((2 * y + 2 - x) * (2 * y + 1 - x) * (2 * y - x) * (2 * y - x - 1))))
      + (-(y + 1) * (x - 2 * (y + 1)) * (x - 2 * (y + 1) + 1) * P x (y + 1))
        * (((x + 2 - y) * (x + 1) * (x + 2)) * (x * (x + 1) * (x + y))
          * ((x + 1) * (x + 2) * (2 * y + 1) * (2 * y + 2)))
      + (-y * (x - 2 * y) * (x - 2 * y + 1) * P x y)
        * (((y + 1) * (x + 1) * (x + 2)) * ((y + 1) * x * (x + 1))
          * ((x + 1) * (x + 2) * (2 * y + 2 - x) * (2 * y + 1 - x))) = 0 := by
  unfold dd c0 c1 c2 P
  ring

lemma cert (n k : ℕ) (hn : 1 ≤ n) :
    dd n * (c0 n * (T n k : ℚ) + c1 n * (T (n + 1) k : ℚ) + c2 n * (T (n + 2) k : ℚ))
      = G n (k + 1) - G n k := by
  rw [T_cast, T_cast, T_cast]
  rw [show n + 1 + k - 1 = n + k by omega, show n + 2 + k - 1 = n + k + 1 by omega]
  unfold G
  rw [show n + (k + 1) - 1 = n + k by omega, show 2 * (k + 1) = 2 * k + 2 by ring]
  push_cast
  have hx : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hy : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  -- the five terms as multiples of the base `b1 b2 b3`
  have f2a : (((n + k - 1).choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1))
      = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * (n : ℚ) * ((n : ℚ) + 1)) := by
    linear_combination ((n : ℚ) + 1) * m2a n k hn
  have f1b : (((n + 1).choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3))
      = (((n + 3).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * ((n : ℚ) + 2 - k) * ((n : ℚ) + 1)) := by
    linear_combination ((n : ℚ) + 1) * m1b n k
  have f2b : (((n + k).choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1))
      = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * ((n : ℚ) + 1) * ((n : ℚ) + k)) := by
    linear_combination (((n : ℚ) + 1) * ((n : ℚ) + k)) * m2b n k
  have f1c : (((n + 2).choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3))
      = (((n + 3).choose (k + 1) : ℕ) : ℚ) * (((k : ℚ) + 1) * ((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
    linear_combination (((n : ℚ) + 1) * ((n : ℚ) + 2)) * m1c n k
  have f2c : (((n + k + 1).choose k : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1))
      = (((n + k + 1).choose (k + 1) : ℕ) : ℚ)
        * (((k : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1)) := by
    linear_combination (((n : ℚ) + k) * ((n : ℚ) + k + 1)) * m2c n k
  have f1d : (((n + 2).choose (k + 1) : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3))
      = (((n + 3).choose (k + 1) : ℕ) : ℚ) * (((n : ℚ) + 2 - k) * ((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
    linear_combination (((n : ℚ) + 1) * ((n : ℚ) + 2)) * m1d n k
  have f2d : (((n + k).choose (k + 1) : ℕ) : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1))
      = (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * ((n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + k)) := by
    linear_combination (((n : ℚ) + 1) * ((n : ℚ) + k)) * m2d n k
  have f3d : (((2 * k + 2).choose n : ℕ) : ℚ)
        * ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4))
      = (((2 * k + 4).choose (n + 2) : ℕ) : ℚ)
        * (((n : ℚ) + 1) * ((n : ℚ) + 2) * (2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2)) := by
    linear_combination ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2)) * m3d n k
  have hF0 := tri ((-1 : ℚ) ^ (n + k)) _ _ _ _ _ _ _ _ _ _ _ _ (m1a n k) f2a (m3a n k)
  have hF1 := tri ((-1 : ℚ) ^ (n + 1 + k)) _ _ _ _ _ _ _ _ _ _ _ _ f1b f2b (m3b n k)
  have hF2 := tri ((-1 : ℚ) ^ (n + 2 + k)) _ _ _ _ _ _ _ _ _ _ _ _ f1c f2c (m3c n k)
  have hG0 := tri ((-1 : ℚ) ^ (n + k)) _ _ _ _ _ _ _ _ _ _ _ _ f1c f2a (m3a n k)
  have hG1 := tri ((-1 : ℚ) ^ (n + (k + 1))) _ _ _ _ _ _ _ _ _ _ _ _ f1d f2d f3d
  have hpoly := poly_id (n : ℚ) (k : ℚ)
  have hD1 : (0 : ℚ) < ((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) := by positivity
  have hD2 : (0 : ℚ) < ((n : ℚ) + 1) * ((n : ℚ) + k) * ((n : ℚ) + k + 1) := by
    apply mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hD3 : (0 : ℚ) < (2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 4) := by
    positivity
  apply mul_right_cancel₀ (mul_pos (mul_pos hD1 hD2) hD3).ne'
  linear_combination (dd (n : ℚ) * c0 (n : ℚ)) * hF0 + (dd (n : ℚ) * c1 (n : ℚ)) * hF1
    + (dd (n : ℚ) * c2 (n : ℚ)) * hF2
    - (-((k : ℚ) + 1) * ((n : ℚ) - 2 * ((k : ℚ) + 1)) * ((n : ℚ) - 2 * ((k : ℚ) + 1) + 1)
        * P (n : ℚ) ((k : ℚ) + 1)) * hG1
    + (-(k : ℚ) * ((n : ℚ) - 2 * k) * ((n : ℚ) - 2 * k + 1) * P (n : ℚ) (k : ℚ)) * hG0
    + ((-1 : ℚ) ^ (n + k) * ((((n + 3).choose (k + 1) : ℕ) : ℚ)
        * (((n + k + 1).choose (k + 1) : ℕ) : ℚ) * (((2 * k + 4).choose (n + 2) : ℕ) : ℚ))) * hpoly

/- ### Telescoping: the recurrence -/

lemma sum_T0 (n : ℕ) : ∑ k ∈ range (n + 3), T n k = s n := by
  have h1 : T n (n + 1) = 0 := by simp [T]
  have h2 : T n (n + 1 + 1) = 0 := by simp [T, Nat.choose_eq_zero_of_lt (by omega : n < n + 1 + 1)]
  rw [s, show n + 3 = n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, h1, h2]
  ring

lemma sum_T1 (n : ℕ) : ∑ k ∈ range (n + 3), T (n + 1) k = s (n + 1) := by
  have h1 : T (n + 1) (n + 1 + 1) = 0 := by
    simp [T]
  rw [s, show n + 3 = n + 1 + 1 + 1 by ring, Finset.sum_range_succ, h1, add_zero]

lemma sum_T2 (n : ℕ) : ∑ k ∈ range (n + 3), T (n + 2) k = s (n + 2) := by
  rw [s, show n + 3 = n + 2 + 1 by ring]

lemma rec_s (n : ℕ) (hn : 1 ≤ n) :
    c0 n * (s n : ℚ) + c1 n * (s (n + 1) : ℚ) + c2 n * (s (n + 2) : ℚ) = 0 := by
  have h : ∀ k ∈ range (n + 3), dd n * (c0 n * (T n k : ℚ) + c1 n * (T (n + 1) k : ℚ)
      + c2 n * (T (n + 2) k : ℚ)) = G n (k + 1) - G n k := fun k _ => cert n k hn
  have hsum := Finset.sum_congr rfl h
  rw [Finset.sum_range_sub] at hsum
  have hG0 : G n 0 = 0 := by simp [G]
  have hG3 : G n (n + 3) = 0 := by simp [G]
  rw [hG0, hG3, sub_zero] at hsum
  have e : ∑ k ∈ range (n + 3), dd n * (c0 n * (T n k : ℚ) + c1 n * (T (n + 1) k : ℚ)
      + c2 n * (T (n + 2) k : ℚ))
      = dd n * (c0 n * (s n : ℚ) + c1 n * (s (n + 1) : ℚ) + c2 n * (s (n + 2) : ℚ)) := by
    rw [← sum_T0 n, ← sum_T1 n, ← sum_T2 n]
    push_cast
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [e] at hsum
  have hn0 : (n : ℚ) ≠ 0 := by have : (1 : ℚ) ≤ n := by exact_mod_cast hn
                               linarith
  have hdd : dd (n : ℚ) ≠ 0 := by
    unfold dd
    exact mul_ne_zero (mul_ne_zero hn0 (by positivity)) (by positivity)
  rcases mul_eq_zero.mp hsum with h0 | h0
  · exact absurd h0 hdd
  · exact h0

/- ### Positivity -/

lemma s_pos_aux (m : ℕ) : 0 < (s (m + 1) : ℚ) ∧ 7 * (s (m + 1) : ℚ) ≤ (s (m + 1 + 1) : ℚ) := by
  induction m with
  | zero =>
    show 0 < ((s 1 : ℤ) : ℚ) ∧ 7 * ((s 1 : ℤ) : ℚ) ≤ ((s 2 : ℤ) : ℚ)
    rw [s_one, s_two]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have hrec := rec_s (m + 1) (by omega)
    rw [show m + 1 + 2 = m + 1 + 1 + 1 by ring] at hrec
    refine ⟨by linarith, ?_⟩
    have hQ : 0 ≤ -7 * c1 ((m + 1 : ℕ) : ℚ) - c0 ((m + 1 : ℕ) : ℚ) - 49 * c2 ((m + 1 : ℕ) : ℚ) := by
      have e : -7 * c1 ((m + 1 : ℕ) : ℚ) - c0 ((m + 1 : ℕ) : ℚ) - 49 * c2 ((m + 1 : ℕ) : ℚ)
          = 390 * (m : ℚ) ^ 5 + 3467 * (m : ℚ) ^ 4 + 12027 * (m : ℚ) ^ 3 + 20365 * (m : ℚ) ^ 2
            + 16815 * (m : ℚ) + 5400 := by
        unfold c0 c1 c2; push_cast; ring
      rw [e]; positivity
    have hc0 : 0 ≤ c0 ((m + 1 : ℕ) : ℚ) := by unfold c0; positivity
    have hc2 : 0 < c2 ((m + 1 : ℕ) : ℚ) := by unfold c2; positivity
    have key : 7 * c2 ((m + 1 : ℕ) : ℚ) * ((s (m + 1 + 1 + 1) : ℚ) - 7 * (s (m + 1 + 1) : ℚ))
        = (-7 * c1 ((m + 1 : ℕ) : ℚ) - c0 ((m + 1 : ℕ) : ℚ) - 49 * c2 ((m + 1 : ℕ) : ℚ))
            * (s (m + 1 + 1) : ℚ)
          + c0 ((m + 1 : ℕ) : ℚ) * ((s (m + 1 + 1) : ℚ) - 7 * (s (m + 1) : ℚ)) := by
      linear_combination 7 * hrec
    have hnn : 0 ≤ 7 * c2 ((m + 1 : ℕ) : ℚ) * ((s (m + 1 + 1 + 1) : ℚ) - 7 * (s (m + 1 + 1) : ℚ)) := by
      rw [key]
      exact add_nonneg (mul_nonneg hQ (by linarith)) (mul_nonneg hc0 (by linarith))
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℚ) < 7 * c2 ((m + 1 : ℕ) : ℚ))).mp hnn
    linarith

lemma s_pos (n : ℕ) (hn : 1 ≤ n) : 0 < s n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact_mod_cast (s_pos_aux m).1

/-- For `n ≥ 1`, the target's `A363983 n` (an `Int.toNat`) is the integer sum itself. -/
theorem cast_A363983 (n : ℕ) (hn : 1 ≤ n) : (_root_.A363983 n : ℤ) = s n := by
  rw [A363983_eq_toNat, Int.toNat_of_nonneg (s_pos n hn).le]

end A363983
