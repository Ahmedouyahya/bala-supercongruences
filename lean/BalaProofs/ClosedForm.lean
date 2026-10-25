import Mathlib

/-!
Lemma 1 of `notes/A361711-proof.md` (milestone M4): the closed form

  `a(2n+1) = (-1)^n C(3n+1, n) C(2n, n)`,   `a(n) = Σ_k (-1)^k C(n,k)^2 C(n-2,k)`.

Route (as in the note, Zeilberger certificate): with `F(n,k) = (-1)^k C(n,k)^2 C(n-2,k)`,
`n = m+2`, every quantity in the certificate identity is `F(m+4,k)` times a polynomial
(this replaces the normalising factor `Φ` of the note by `F(m+4,k)/d(m)`), the certificate
identity becomes a polynomial identity (`ring`), it telescopes to the 3-term recurrence
`c₀(n) a(n) + c₁(n) a(n+1) + c₂(n) a(n+2) = 0` (`n ≥ 2`), the closed forms for both parities
satisfy the same recurrence, and the initial values `a(2) = 1`, `a(3) = -8` agree.
-/

open Finset

namespace Bala

/-- the summand `F(n,k) = (-1)^k C(n,k)^2 C(n-2,k)` as a rational number -/
noncomputable def F (n k : ℕ) : ℚ := (-1) ^ k * (n.choose k : ℚ) ^ 2 * ((n - 2).choose k : ℚ)

/-- `a(n) = Σ_{k ≤ n} F(n,k)` (the terms `k = n-1, n` vanish) -/
noncomputable def aQ (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), F n k

/-- the certificate numerator `P(n,k)` (Appendix A of the note) -/
def P (n k : ℚ) : ℚ :=
  84*n^8 - 234*k*n^7 + 520*n^7 + 261*k^2*n^6 - 1215*k*n^6 + 1306*n^6 - 135*k^3*n^5
  + 1101*k^2*n^5 - 2590*k*n^5 + 1772*n^5 + 27*k^4*n^4 - 441*k^3*n^4 + 1934*k^2*n^4
  - 3042*k*n^4 + 1454*n^4 + 63*k^4*n^3 - 606*k^3*n^3 + 1870*k^2*n^3 - 2183*k*n^3 + 752*n^3
  + 60*k^4*n^2 - 434*k^3*n^2 + 1062*k^2*n^2 - 1000*k*n^2 + 268*n^2 + 26*k^4*n - 160*k^3*n
  + 344*k^2*n - 296*k*n + 80*n + 4*k^4 - 24*k^3 + 52*k^2 - 48*k + 16

/-- recurrence coefficients -/
def c0 (n : ℚ) : ℚ := -(3*(n-1)*n*(3*n+1)*(3*n+2)*(3*n^2+4*n+2))
def c1 (n : ℚ) : ℚ := -(6*n*(6*n^3+12*n^2+5*n+1))
def c2 (n : ℚ) : ℚ := -(n^2*(n+2)^2*(3*n^2-2*n+1))

/-- `d(m) = (n+2)^2 (n+1)^2 n (n-1)` with `n = m+2` -/
def dd (m : ℚ) : ℚ := (m+4)^2*(m+3)^2*(m+2)*(m+1)

/-- the telescoping term `G(n,k)` (times `d`), with `n = m+2` -/
noncomputable def G (m k : ℕ) : ℚ := F (m+4) k * (k:ℚ)^3 * ((m:ℚ)+1) * P ((m:ℚ)+2) k

/-! ### absorption identities for binomial coefficients, in `ℚ` -/

theorem choose_mul_succ_q (n k : ℕ) (h : k ≤ n + 1) :
    ((n+1).choose k : ℚ) * ((n:ℚ) + 1 - k) = (n.choose k : ℚ) * ((n:ℚ) + 1) := by
  have h1 := Nat.choose_mul_succ_eq n k
  have h2 : ((n + 1 - k : ℕ) : ℚ) = (n:ℚ) + 1 - k := by
    rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
  rw [← h2]
  exact_mod_cast h1.symm

theorem choose_succ_right_q (n k : ℕ) (h : k ≤ n) :
    (n.choose (k+1) : ℚ) * ((k:ℚ) + 1) = (n.choose k : ℚ) * ((n:ℚ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℚ) = (n:ℚ) - k := by rw [Nat.cast_sub h]
  rw [← h2]
  exact_mod_cast h1

theorem succ_mul_choose_q (n k : ℕ) :
    ((n:ℚ) + 1) * (n.choose k : ℚ) = ((n+1).choose (k+1) : ℚ) * ((k:ℚ) + 1) := by
  have h1 := Nat.add_one_mul_choose_eq n k
  exact_mod_cast h1

theorem choose_absorb2 (m k : ℕ) (h : k ≤ m + 2) :
    ((m+2).choose k : ℚ) * ((m:ℚ) + 2 - k) * ((m:ℚ) + 1 - k)
      = (m.choose k : ℚ) * (((m:ℚ) + 2) * ((m:ℚ) + 1)) := by
  rcases Nat.lt_or_ge k (m + 2) with hk | hk
  · have h1 := choose_mul_succ_q (m+1) k (by omega)
    have h2 := choose_mul_succ_q m k (by omega)
    rw [show m + 1 + 1 = m + 2 from rfl] at h1
    push_cast at h1
    linear_combination ((m:ℚ) + 1 - k) * h1 + ((m:ℚ) + 2) * h2
  · have hk' : k = m + 2 := by omega
    subst hk'
    rw [Nat.choose_eq_zero_of_lt (by omega : m < m + 2)]
    simp

/-! ### unfolding `F` at shifted arguments -/

theorem F_add_two (m k : ℕ) :
    F (m+2) k = (-1)^k * ((m+2).choose k : ℚ)^2 * (m.choose k : ℚ) := by
  unfold F
  rw [show m + 2 - 2 = m by omega]

theorem F_add_three (m k : ℕ) :
    F (m+3) k = (-1)^k * ((m+3).choose k : ℚ)^2 * ((m+1).choose k : ℚ) := by
  unfold F
  rw [show m + 3 - 2 = m + 1 by omega]

theorem F_add_four (m k : ℕ) :
    F (m+4) k = (-1)^k * ((m+4).choose k : ℚ)^2 * ((m+2).choose k : ℚ) := by
  unfold F
  rw [show m + 4 - 2 = m + 2 by omega]

/-! ### the relations `F(n,k)·d = F(n+2,k)·q₀`, `F(n+1,k)·d = F(n+2,k)·q₁`, and the term ratio -/

theorem R1 (m k : ℕ) (hk : k ≤ m + 2) :
    F (m+2) k * dd m = F (m+4) k *
      (((m:ℚ)+4-k)^2 * ((m:ℚ)+3-k)^2 * ((m:ℚ)+2-k) * ((m:ℚ)+1-k)) := by
  have hA := choose_absorb2 (m+2) k (by omega)
  have hB := choose_absorb2 m k hk
  rw [show m + 2 + 2 = m + 4 from rfl] at hA
  push_cast at hA
  rw [F_add_two, F_add_four]
  unfold dd
  linear_combination
    (-(-1:ℚ)^k * (((m+4).choose k : ℚ) * ((m:ℚ)+2+2-k) * ((m:ℚ)+2+1-k)
        + ((m+2).choose k : ℚ) * (((m:ℚ)+2+2) * ((m:ℚ)+2+1)))
      * (((m+2).choose k : ℚ) * ((m:ℚ)+2-k) * ((m:ℚ)+1-k))) * hA
    + (-(-1:ℚ)^k * (((m+2).choose k : ℚ) * (((m:ℚ)+2+2) * ((m:ℚ)+2+1)))^2) * hB

theorem R2 (m k : ℕ) (hk : k ≤ m + 2) :
    F (m+3) k * dd m = F (m+4) k *
      (((m:ℚ)+3)^2 * ((m:ℚ)+1) * ((m:ℚ)+4-k)^2 * ((m:ℚ)+2-k)) := by
  have hA := choose_mul_succ_q (m+3) k (by omega)
  have hB := choose_mul_succ_q (m+1) k (by omega)
  rw [show m + 3 + 1 = m + 4 from rfl] at hA
  rw [show m + 1 + 1 = m + 2 from rfl] at hB
  push_cast at hA hB
  rw [F_add_three, F_add_four]
  unfold dd
  linear_combination
    (-(-1:ℚ)^k * (((m:ℚ)+3)^2 * ((m:ℚ)+1))
      * (((m+4).choose k : ℚ) * ((m:ℚ)+3+1-k) + ((m+3).choose k : ℚ) * ((m:ℚ)+3+1))
      * (((m+2).choose k : ℚ) * ((m:ℚ)+1+1-k))) * hA
    + (-(-1:ℚ)^k * (((m:ℚ)+3)^2 * ((m:ℚ)+1))
      * (((m+3).choose k : ℚ) * ((m:ℚ)+3+1))^2) * hB

theorem R4 (m k : ℕ) (hk : k ≤ m + 2) :
    F (m+4) (k+1) * ((k:ℚ)+1)^3 = -F (m+4) k * ((m:ℚ)+4-k)^2 * ((m:ℚ)+2-k) := by
  have hA := choose_succ_right_q (m+4) k (by omega)
  have hB := choose_succ_right_q (m+2) k hk
  push_cast at hA hB
  rw [F_add_four, F_add_four]
  linear_combination
    ((-1:ℚ)^(k+1) * (((m+4).choose (k+1) : ℚ) * ((k:ℚ)+1) + ((m+4).choose k : ℚ) * ((m:ℚ)+4-k))
      * (((m+2).choose (k+1) : ℚ) * ((k:ℚ)+1))) * hA
    + ((-1:ℚ)^(k+1) * (((m+4).choose k : ℚ) * ((m:ℚ)+4-k))^2) * hB

/-! ### the certificate identity -/

theorem cert (m k : ℕ) (hk : k ≤ m + 2) :
    dd m * (c0 ((m:ℚ)+2) * F (m+2) k + c1 ((m:ℚ)+2) * F (m+3) k + c2 ((m:ℚ)+2) * F (m+4) k)
      = G m (k+1) - G m k := by
  have r1 := R1 m k hk
  have r2 := R2 m k hk
  have r4 := R4 m k hk
  unfold G
  push_cast
  unfold c0 c1 c2 P dd at *
  linear_combination
    (-(3*(((m:ℚ)+2)-1)*((m:ℚ)+2)*(3*((m:ℚ)+2)+1)*(3*((m:ℚ)+2)+2)*(3*((m:ℚ)+2)^2+4*((m:ℚ)+2)+2))) * r1
    + (-(6*((m:ℚ)+2)*(6*((m:ℚ)+2)^3+12*((m:ℚ)+2)^2+5*((m:ℚ)+2)+1))) * r2
    + (-((m:ℚ)+1) * (84*((m:ℚ)+2)^8 - 234*((k:ℚ)+1)*((m:ℚ)+2)^7 + 520*((m:ℚ)+2)^7
        + 261*((k:ℚ)+1)^2*((m:ℚ)+2)^6 - 1215*((k:ℚ)+1)*((m:ℚ)+2)^6 + 1306*((m:ℚ)+2)^6
        - 135*((k:ℚ)+1)^3*((m:ℚ)+2)^5 + 1101*((k:ℚ)+1)^2*((m:ℚ)+2)^5 - 2590*((k:ℚ)+1)*((m:ℚ)+2)^5
        + 1772*((m:ℚ)+2)^5 + 27*((k:ℚ)+1)^4*((m:ℚ)+2)^4 - 441*((k:ℚ)+1)^3*((m:ℚ)+2)^4
        + 1934*((k:ℚ)+1)^2*((m:ℚ)+2)^4 - 3042*((k:ℚ)+1)*((m:ℚ)+2)^4 + 1454*((m:ℚ)+2)^4
        + 63*((k:ℚ)+1)^4*((m:ℚ)+2)^3 - 606*((k:ℚ)+1)^3*((m:ℚ)+2)^3 + 1870*((k:ℚ)+1)^2*((m:ℚ)+2)^3
        - 2183*((k:ℚ)+1)*((m:ℚ)+2)^3 + 752*((m:ℚ)+2)^3 + 60*((k:ℚ)+1)^4*((m:ℚ)+2)^2
        - 434*((k:ℚ)+1)^3*((m:ℚ)+2)^2 + 1062*((k:ℚ)+1)^2*((m:ℚ)+2)^2 - 1000*((k:ℚ)+1)*((m:ℚ)+2)^2
        + 268*((m:ℚ)+2)^2 + 26*((k:ℚ)+1)^4*((m:ℚ)+2) - 160*((k:ℚ)+1)^3*((m:ℚ)+2)
        + 344*((k:ℚ)+1)^2*((m:ℚ)+2) - 296*((k:ℚ)+1)*((m:ℚ)+2) + 80*((m:ℚ)+2) + 4*((k:ℚ)+1)^4
        - 24*((k:ℚ)+1)^3 + 52*((k:ℚ)+1)^2 - 48*((k:ℚ)+1) + 16)) * r4

/-! ### telescoping: the recurrence for `aQ` -/

theorem aQ_add_two (m : ℕ) : aQ (m+2) = ∑ k ∈ range (m+3), F (m+2) k := rfl

theorem aQ_add_two' (m : ℕ) : aQ (m+2) = ∑ k ∈ range (m+1), F (m+2) k := by
  unfold aQ
  rw [sum_range_succ, sum_range_succ, F_add_two, F_add_two,
    Nat.choose_eq_zero_of_lt (by omega : m < m + 1),
    Nat.choose_eq_zero_of_lt (by omega : m < m + 2)]
  simp

theorem aQ_add_three (m : ℕ) : aQ (m+3) = ∑ k ∈ range (m+3), F (m+3) k := by
  unfold aQ
  rw [sum_range_succ, F_add_three, Nat.choose_eq_zero_of_lt (by omega : m + 1 < m + 3)]
  simp

theorem aQ_add_four (m : ℕ) : aQ (m+4) = ∑ k ∈ range (m+3), F (m+4) k := by
  unfold aQ
  rw [sum_range_succ, sum_range_succ, F_add_four, F_add_four,
    Nat.choose_eq_zero_of_lt (by omega : m + 2 < m + 3),
    Nat.choose_eq_zero_of_lt (by omega : m + 2 < m + 4)]
  simp

theorem rec_sum (m : ℕ) :
    dd m * (c0 ((m:ℚ)+2) * aQ (m+2) + c1 ((m:ℚ)+2) * aQ (m+3) + c2 ((m:ℚ)+2) * aQ (m+4)) = 0 := by
  have h : ∀ k ∈ range (m+3),
      dd m * (c0 ((m:ℚ)+2) * F (m+2) k + c1 ((m:ℚ)+2) * F (m+3) k + c2 ((m:ℚ)+2) * F (m+4) k)
        = G m (k+1) - G m k := by
    intro k hk
    exact cert m k (by have := mem_range.mp hk; omega)
  have hsum := sum_congr rfl h
  rw [sum_range_sub] at hsum
  have hG0 : G m 0 = 0 := by simp [G]
  have hG1 : G m (m+3) = 0 := by
    unfold G
    rw [F_add_four, Nat.choose_eq_zero_of_lt (by omega : m + 2 < m + 3)]
    simp
  rw [hG0, hG1, sub_zero] at hsum
  rw [aQ_add_two, aQ_add_three, aQ_add_four]
  refine Eq.trans ?_ hsum
  simp only [mul_add, mul_sum, sum_add_distrib]

theorem dd_ne_zero (m : ℕ) : dd m ≠ 0 := by
  unfold dd
  positivity

theorem rec_aQ (m : ℕ) :
    c0 ((m:ℚ)+2) * aQ (m+2) + c1 ((m:ℚ)+2) * aQ (m+3) + c2 ((m:ℚ)+2) * aQ (m+4) = 0 := by
  have h := rec_sum m
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (dd_ne_zero m)
  · exact h0

/-! ### the closed forms and their recurrence -/

/-- odd closed form `b(2M+1) = (-1)^M C(3M+1, M) C(2M, M)` -/
noncomputable def bO (M : ℕ) : ℚ :=
  (-1) ^ M * ((3 * M + 1).choose M : ℚ) * ((2 * M).choose M : ℚ)

/-- even closed form `b(2M) = (-1)^M (2M-3)/(6(2M-1)) C(3M, M) C(2M, M)` -/
noncomputable def bE (M : ℕ) : ℚ :=
  (-1) ^ M * ((2 * (M:ℚ) - 3) / (6 * (2 * (M:ℚ) - 1))) * ((3 * M).choose M : ℚ)
    * ((2 * M).choose M : ℚ)

theorem ratio_X1 (M : ℕ) :
    ((3 * M + 1).choose M : ℚ) = ((3 * M).choose M : ℚ) * (3 * (M:ℚ) + 1) / (2 * (M:ℚ) + 1) := by
  have h := choose_mul_succ_q (3 * M) M (by omega)
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination h

theorem ratio_X2 (M : ℕ) :
    ((3 * M + 2).choose M : ℚ) = ((3 * M + 1).choose M : ℚ) * (3 * (M:ℚ) + 2) / (2 * (M:ℚ) + 2) := by
  have h := choose_mul_succ_q (3 * M + 1) M (by omega)
  rw [show 3 * M + 1 + 1 = 3 * M + 2 from rfl] at h
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination h

theorem ratio_X3 (M : ℕ) :
    ((3 * M + 3).choose (M + 1) : ℚ)
      = ((3 * M + 2).choose M : ℚ) * (3 * (M:ℚ) + 3) / ((M:ℚ) + 1) := by
  have h := succ_mul_choose_q (3 * M + 2) M
  rw [show 3 * M + 2 + 1 = 3 * M + 3 from rfl] at h
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination -h

theorem ratio_X4 (M : ℕ) :
    ((3 * M + 4).choose (M + 1) : ℚ)
      = ((3 * M + 3).choose (M + 1) : ℚ) * (3 * (M:ℚ) + 4) / (2 * (M:ℚ) + 3) := by
  have h := choose_mul_succ_q (3 * M + 3) (M + 1) (by omega)
  rw [show 3 * M + 3 + 1 = 3 * M + 4 from rfl] at h
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination h

theorem ratio_Y1 (M : ℕ) :
    ((2 * M + 1).choose M : ℚ) = ((2 * M).choose M : ℚ) * (2 * (M:ℚ) + 1) / ((M:ℚ) + 1) := by
  have h := choose_mul_succ_q (2 * M) M (by omega)
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination h

theorem ratio_Y2 (M : ℕ) :
    ((2 * M + 2).choose (M + 1) : ℚ)
      = ((2 * M + 1).choose M : ℚ) * (2 * (M:ℚ) + 2) / ((M:ℚ) + 1) := by
  have h := succ_mul_choose_q (2 * M + 1) M
  rw [show 2 * M + 1 + 1 = 2 * M + 2 from rfl] at h
  push_cast at h
  apply eq_div_of_mul_eq (by positivity)
  linear_combination -h

theorem two_M_sub_one_ne_zero (M : ℕ) (hM : 1 ≤ M) : (2 * (M:ℚ) - 1) ≠ 0 := by
  have : (1:ℚ) ≤ M := by exact_mod_cast hM
  intro h
  linarith

/-- the even-index recurrence for the closed forms (`n = 2M`, `M ≥ 1`) -/
theorem recE (M : ℕ) (hM : 1 ≤ M) :
    c0 (2 * (M:ℚ)) * bE M + c1 (2 * (M:ℚ)) * bO M + c2 (2 * (M:ℚ)) * bE (M + 1) = 0 := by
  unfold bE bO c0 c1 c2
  rw [show 3 * (M + 1) = 3 * M + 3 by ring, show 2 * (M + 1) = 2 * M + 2 by ring]
  rw [ratio_X3, ratio_X2, ratio_X1, ratio_Y2, ratio_Y1]
  push_cast
  have h1 := two_M_sub_one_ne_zero M hM
  have h2 : (2 * ((M:ℚ) + 1) - 1) ≠ 0 := by
    have : (1:ℚ) ≤ M := by exact_mod_cast hM
    intro h; linarith
  have h3 : (2 * (M:ℚ) + 1) ≠ 0 := by positivity
  have h4 : (2 * (M:ℚ) + 2) ≠ 0 := by positivity
  have h5 : ((M:ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- the odd-index recurrence for the closed forms (`n = 2M+1`, `M ≥ 1`) -/
theorem recO (M : ℕ) (hM : 1 ≤ M) :
    c0 (2 * (M:ℚ) + 1) * bO M + c1 (2 * (M:ℚ) + 1) * bE (M + 1)
      + c2 (2 * (M:ℚ) + 1) * bO (M + 1) = 0 := by
  unfold bE bO c0 c1 c2
  rw [show 3 * (M + 1) = 3 * M + 3 by ring, show 2 * (M + 1) = 2 * M + 2 by ring,
    show 3 * M + 3 + 1 = 3 * M + 4 from rfl]
  rw [ratio_X4, ratio_X3, ratio_X2, ratio_X1, ratio_Y2, ratio_Y1]
  push_cast
  have h1 := two_M_sub_one_ne_zero M hM
  have h2 : (2 * ((M:ℚ) + 1) - 1) ≠ 0 := by
    have : (1:ℚ) ≤ M := by exact_mod_cast hM
    intro h; linarith
  have h3 : (2 * (M:ℚ) + 1) ≠ 0 := by positivity
  have h4 : (2 * (M:ℚ) + 2) ≠ 0 := by positivity
  have h5 : ((M:ℚ) + 1) ≠ 0 := by positivity
  have h6 : (2 * (M:ℚ) + 3) ≠ 0 := by positivity
  field_simp
  ring

theorem c2_ne_zero (n : ℚ) (hn : 1 ≤ n) : c2 n ≠ 0 := by
  unfold c2
  have h1 : 3*n^2 - 2*n + 1 = 2*n^2 + (n-1)^2 := by ring
  rw [h1]
  have h3 : 0 < n := by linarith
  have h4 : 0 < n^2 * (n+2)^2 * (2*n^2 + (n-1)^2) := by positivity
  exact neg_ne_zero.mpr h4.ne'

/-! ### initial values -/

theorem aQ_two : aQ 2 = 1 := by
  norm_num [aQ, F, sum_range_succ]

theorem aQ_three : aQ 3 = -8 := by
  norm_num [aQ, F, sum_range_succ, Nat.choose]

theorem bE_one : bE 1 = 1 := by
  norm_num [bE]

theorem bO_one : bO 1 = -8 := by
  norm_num [bO]

/-! ### uniqueness: strong induction -/

theorem aQ_closed (M : ℕ) : aQ (2*M+2) = bE (M+1) ∧ aQ (2*M+3) = bO (M+1) := by
  induction M with
  | zero =>
    refine ⟨?_, ?_⟩
    · show aQ 2 = bE 1
      rw [aQ_two, bE_one]
    · show aQ 3 = bO 1
      rw [aQ_three, bO_one]
  | succ M ih =>
    obtain ⟨h1, h2⟩ := ih
    have hM : 1 ≤ M + 1 := by omega
    -- first step: n = 2M+2
    have rE := recE (M+1) hM
    have rA := rec_aQ (2*M)
    push_cast at rE rA
    have e1 : aQ (2*M+4) = bE (M+2) := by
      have hc := c2_ne_zero (2*((M:ℚ)+1)) (by linarith [(Nat.cast_nonneg M : (0:ℚ) ≤ M)])
      have key : c2 (2*((M:ℚ)+1)) * (aQ (2*M+4) - bE (M+2)) = 0 := by
        have e : (2:ℚ)*(M:ℚ)+2 = 2*((M:ℚ)+1) := by ring
        rw [e] at rA
        rw [h1, h2] at rA
        rw [show M + 1 + 1 = M + 2 from rfl] at rE
        linear_combination rA - rE
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hc
      · linarith
    -- second step: n = 2M+3
    have rO := recO (M+1) hM
    have rA' := rec_aQ (2*M+1)
    push_cast at rO rA'
    have e2 : aQ (2*M+5) = bO (M+2) := by
      have hc := c2_ne_zero (2*((M:ℚ)+1)+1) (by linarith [(Nat.cast_nonneg M : (0:ℚ) ≤ M)])
      have key : c2 (2*((M:ℚ)+1)+1) * (aQ (2*M+5) - bO (M+2)) = 0 := by
        have e : (2:ℚ)*(M:ℚ)+1+2 = 2*((M:ℚ)+1)+1 := by ring
        rw [e] at rA'
        rw [show 2*M+1+2 = 2*M+3 from rfl, show 2*M+1+3 = 2*M+4 from rfl,
          show 2*M+1+4 = 2*M+5 from rfl] at rA'
        rw [h2, e1] at rA'
        rw [show M + 1 + 1 = M + 2 from rfl] at rO
        linear_combination rA' - rO
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hc
      · linarith
    refine ⟨?_, ?_⟩
    · rw [show 2*(M+1)+2 = 2*M+4 by ring, show M + 1 + 1 = M + 2 from rfl]
      exact e1
    · rw [show 2*(M+1)+3 = 2*M+5 by ring, show M + 1 + 1 = M + 2 from rfl]
      exact e2

/-- **Lemma 1** (closed form at odd arguments): `aQ (2n+1) = (-1)^n C(3n+1,n) C(2n,n)`. -/
theorem aQ_odd (n : ℕ) : aQ (2*n+1) = bO n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aQ, bO, F, sum_range_succ]
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
    have := (aQ_closed M).2
    rw [show 2*(M+1)+1 = 2*M+3 by ring]
    exact this

end Bala
