import BalaProofs.EpochA333042

/-!
# Theorem F (p ≥ 5), Lean route b — set-up (PLAN-route-b.md, definitions and step 1)

Theorem F: for a prime `p ≥ 5`, integers `a b`, `c : ℕ`, `M ≥ 1`, with
`A(N) := [x^{cN}] ((1+x)^a (1-x)^b)^N`, one has `v_p(A(pM) - A(M)) ≥ 3 (1 + v_p M)`.

Everything is built on Epoch AI's power-series exponential `expS` and the valuation predicate
`V p k q` (`v_p(q) ≥ k`) from `BalaCheck.EpochExp` (namespace `Epoch333042.Super`).
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- `log(1+x)`. -/
def lp : ℚ⟦X⟧ := mk fun j => if j = 0 then 0 else (-1 : ℚ) ^ (j + 1) / (j : ℚ)

/-- `log(1-x)`. -/
def lm : ℚ⟦X⟧ := mk fun j => if j = 0 then 0 else -1 / (j : ℚ)

/-- coefficients of `F = a log(1+x) + b log(1-x)`. -/
def fc (a b : ℤ) (j : ℕ) : ℚ := if j = 0 then 0 else ((a : ℚ) * (-1) ^ (j + 1) - b) / (j : ℚ)

/-- `F = a log(1+x) + b log(1-x) = log φ`, `φ = (1+x)^a (1-x)^b`. -/
def F (a b : ℤ) : ℚ⟦X⟧ := mk (fc a b)

/-- `Phi a b N = φ^N = exp (N F)`. -/
def Phi (a b : ℤ) (N : ℕ) : ℚ⟦X⟧ := expS ((N : ℚ) • F a b)

/-- `A(N) = [x^{cN}] φ^N`. -/
def A (a b : ℤ) (c N : ℕ) : ℚ := coeff (c * N) (Phi a b N)

/-- coefficients of the reduced logarithm `L = a V - b U` (the terms of `F` at exponents prime to `p`). -/
def Lc (p : ℕ) (a b : ℤ) (j : ℕ) : ℚ := if p ∣ j then 0 else fc a b j

/-- the reduced logarithm `L`. -/
def L (p : ℕ) (a b : ℤ) : ℚ⟦X⟧ := mk (Lc p a b)

/-- `p`-integrality of all coefficients. -/
def PInt (p : ℕ) (G : ℚ⟦X⟧) : Prop := ∀ j, V p 0 (coeff j G)

theorem F_eq (a b : ℤ) : F a b = (a : ℚ) • lp + (b : ℚ) • lm := by
  ext j
  simp only [F, lp, lm, fc, coeff_mk, map_add, coeff_smul, smul_eq_mul]
  split_ifs with h
  · simp
  · ring

theorem expS_lp : expS lp = 1 + X := by
  symm
  apply IsExpOf.eq_expS
  rw [isExpOf_iff_deriv]
  refine ⟨by simp, ?_⟩
  ext n
  rw [map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_add, mul_one, map_add]
  rcases n with _ | n
  · rw [coeff_zero_mul_X, add_zero, coeff_derivative]
    simp [lp]
  · rw [coeff_succ_mul_X, coeff_derivative, coeff_derivative, coeff_one, if_neg (by omega)]
    simp only [lp, coeff_mk, if_neg (show n + 1 + 1 ≠ 0 by omega),
      if_neg (show n + 1 ≠ 0 by omega)]
    push_cast
    field_simp
    ring

theorem expS_lm : expS lm = 1 - X := by
  symm
  apply IsExpOf.eq_expS
  rw [isExpOf_iff_deriv]
  refine ⟨by simp, ?_⟩
  ext n
  rw [map_sub, Derivation.map_one_eq_zero, derivative_X, zero_sub, mul_sub, mul_one, map_sub,
    map_neg]
  rcases n with _ | n
  · rw [coeff_zero_mul_X, sub_zero, coeff_derivative]
    simp [lm]
  · rw [coeff_succ_mul_X, coeff_derivative, coeff_derivative, coeff_one, if_neg (by omega)]
    simp only [lm, coeff_mk, if_neg (show n + 1 + 1 ≠ 0 by omega),
      if_neg (show n + 1 ≠ 0 by omega)]
    push_cast
    field_simp
    ring

theorem inv_unique {G H H' : ℚ⟦X⟧} (h : G * H = 1) (h' : G * H' = 1) : H = H' := by
  calc H = H * (G * H') := by rw [h', mul_one]
  _ = (G * H) * H' := by ring
  _ = H' := by rw [h, one_mul]

theorem one_sub_X_mul_c1S : (1 - X : ℚ⟦X⟧) * c1S = 1 := by
  have h := c1S_eq
  calc (1 - X) * c1S = c1S - X * c1S := by ring
  _ = 1 := by rw [sub_eq_iff_eq_add]; exact h

theorem expS_neg_lm : expS (-lm) = c1S := by
  have h := expS_mul_expS_neg lm
  rw [expS_lm] at h
  exact inv_unique h one_sub_X_mul_c1S

theorem expS_neg_lp : expS (-lp) = expand 2 two_ne_zero c1S * (1 - X) := by
  have h := expS_mul_expS_neg lp
  rw [expS_lp] at h
  refine inv_unique h ?_
  have h2 : expand 2 two_ne_zero (c1S * (1 - X)) = 1 := by
    rw [mul_comm, one_sub_X_mul_c1S, map_one]
  rw [map_mul, map_sub, map_one, expand_X] at h2
  calc (1 + X) * (expand 2 two_ne_zero c1S * (1 - X))
      = expand 2 two_ne_zero c1S * (1 - X ^ 2) := by ring
  _ = 1 := h2

theorem Phi_eq_pow (a b : ℤ) (N : ℕ) : Phi a b N = (expS (F a b)) ^ N := by
  rw [Phi, Nat.cast_smul_eq_nsmul ℚ, expS_nsmul]

theorem Phi_eq_expS (a b : ℤ) (N : ℕ) :
    Phi a b N = expS (((N * a : ℤ) : ℚ) • lp) * expS (((N * b : ℤ) : ℚ) • lm) := by
  rw [Phi, F_eq, smul_add, smul_smul, smul_smul, expS_add]
  simp only [Int.cast_mul, Int.cast_natCast]

section int

variable {p : ℕ} [hp : Fact p.Prime]

theorem pint_one : PInt p (1 : ℚ⟦X⟧) := by
  intro j
  exact V_coeff_one

theorem pint_mul {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H) : PInt p (G * H) := by
  intro j
  simpa using V_coeff_mul hG hH j

theorem pint_pow {G : ℚ⟦X⟧} (hG : PInt p G) (n : ℕ) : PInt p (G ^ n) := by
  intro j
  simpa using V_coeff_pow hG n j

theorem pint_sub {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H) : PInt p (G - H) := by
  intro j
  rw [map_sub]
  exact V_sub (hG j) (hH j)

theorem pint_add {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H) : PInt p (G + H) := by
  intro j
  rw [map_add]
  exact V_add (hG j) (hH j)

theorem pint_X : PInt p (X : ℚ⟦X⟧) := by
  intro j
  rw [coeff_X]
  split
  · exact V_one
  · exact V_zero_val _

theorem pint_expS_zsmul {G : ℚ⟦X⟧} (hG : PInt p (expS G)) (z : ℤ) :
    PInt p (expS ((z : ℚ) • G)) := by
  have hn : ∀ n : ℕ, PInt p (expS ((n : ℚ) • G)) := by
    intro n
    rw [Nat.cast_smul_eq_nsmul ℚ, expS_nsmul]
    exact pint_pow hG n
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast]
    exact hn n
  · rw [Int.cast_neg, Int.cast_natCast, neg_smul]
    exact fun j => V_coeff_div (expS_mul_expS_neg ((n : ℚ) • G)) (constantCoeff_expS _) (hn n)
      pint_one j

theorem pint_Phi (a b : ℤ) (N : ℕ) : PInt p (Phi a b N) := by
  rw [Phi_eq_expS]
  refine pint_mul (pint_expS_zsmul ?_ _) (pint_expS_zsmul ?_ _)
  · rw [expS_lp]; exact pint_add pint_one pint_X
  · rw [expS_lm]; exact pint_sub pint_one pint_X

theorem pint_expS_F (a b : ℤ) : PInt p (expS (F a b)) := by
  have h := pint_Phi (p := p) a b 1
  rwa [Phi, Nat.cast_one, one_smul] at h

end int

end

end TF
