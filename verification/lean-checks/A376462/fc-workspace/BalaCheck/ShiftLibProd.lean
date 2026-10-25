import BalaCheck.OSSLib

/-!
# A376462 shifted congruence, lemma bank §1: exact product identities and expansions

Proof note: `proofs/A376462-shifted-congruence.md`, §1 (Lemmas 1.1–1.3).

Conventions (all in `ℤ_[p]`).
* `Ring.inverse (k : ℤ_[p])` is `1/k` for `p ∤ k` and `0` for `p ∣ k`, so sums and products of
  `Ring.inverse k` over `range (x + 1)` are automatically the primed sums/products `Σ′`, `Π′`
  of the note (indices prime to `p`; the index `0` contributes `0`, resp. the factor `1`).
* `H p n = H′_n`, `S p d x = S_d(x)` (`d ≥ 1`), `Pm p L x = Π′_{λ≤x}(1 - L/λ)`,
  `Pp p L x = Π′_{λ≤x}(1 + L/λ)`.
* Binomials with negative upper argument are written through `ℕ`-binomials (for `L ≥ 1`):
  `(-1)^n C(-L-1, n) = C(L+n, n)`, `(-1)^n C(-L, n) = C(L+n-1, n)`.
  Lemma 1.1 is proved for `m ≥ 1` in this form, which covers both signs `±m` of the note.
-/

open Nat Finset

namespace ShiftLib

section prod

variable (p : ℕ) [Fact p.Prime]

/- ### `Ring.inverse` on naturals -/

lemma inv_eq_zero_of_dvd {k : ℕ} (h : p ∣ k) : Ring.inverse (k : ℤ_[p]) = 0 := by
  apply Ring.inverse_non_unit
  intro hu
  have h1 : (p : ℤ_[p]) ∣ (k : ℤ_[p]) := by exact_mod_cast Nat.cast_dvd_cast h
  have h2 : ‖(k : ℤ_[p])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr h1
  rw [PadicInt.isUnit_iff] at hu
  linarith

lemma mul_inv_nat {k : ℕ} (h : ¬ p ∣ k) : (k : ℤ_[p]) * Ring.inverse (k : ℤ_[p]) = 1 :=
  Ring.mul_inverse_cancel _ (Epoch361883.isUnit_nat_of_not_dvd p h)

/- ### Definitions -/

/-- `H′_n = Σ′_{λ ≤ n} 1/λ`. -/
noncomputable def H (n : ℕ) : ℤ_[p] := ∑ k ∈ range (n + 1), Ring.inverse (k : ℤ_[p])

/-- `S_d(x) = Σ′_{μ ≤ x} μ^{-d}` (meaningful for `d ≥ 1`). -/
noncomputable def S (d x : ℕ) : ℤ_[p] := ∑ k ∈ range (x + 1), Ring.inverse (k : ℤ_[p]) ^ d

/-- `P_x = Π′_{λ ≤ x} (1 - L/λ)`. -/
noncomputable def Pm (L : ℤ_[p]) (x : ℕ) : ℤ_[p] :=
  ∏ k ∈ range (x + 1), (1 - L * Ring.inverse (k : ℤ_[p]))

/-- `P̄_x = Π′_{λ ≤ x} (1 + L/λ)`. -/
noncomputable def Pp (L : ℤ_[p]) (x : ℕ) : ℤ_[p] :=
  ∏ k ∈ range (x + 1), (1 + L * Ring.inverse (k : ℤ_[p]))

lemma Pm_succ (L : ℤ_[p]) (x : ℕ) :
    Pm p L (x + 1) = Pm p L x * (1 - L * Ring.inverse (((x + 1 : ℕ)) : ℤ_[p])) := by
  unfold Pm; rw [Finset.prod_range_succ]

lemma Pp_succ (L : ℤ_[p]) (x : ℕ) :
    Pp p L (x + 1) = Pp p L x * (1 + L * Ring.inverse (((x + 1 : ℕ)) : ℤ_[p])) := by
  unfold Pp; rw [Finset.prod_range_succ]

lemma Pm_succ_of_dvd (L : ℤ_[p]) (x : ℕ) (h : p ∣ x + 1) : Pm p L (x + 1) = Pm p L x := by
  rw [Pm_succ, inv_eq_zero_of_dvd p h, mul_zero, sub_zero, mul_one]

lemma Pp_succ_of_dvd (L : ℤ_[p]) (x : ℕ) (h : p ∣ x + 1) : Pp p L (x + 1) = Pp p L x := by
  rw [Pp_succ, inv_eq_zero_of_dvd p h, mul_zero, add_zero, mul_one]

/- ### Lemma 1.1 (exact), `L = m p^s`, `L′ = m p^(s-1)` -/

lemma cast_choose_succ_right (N k : ℕ) :
    ((N.choose (k + 1) : ℕ) : ℤ_[p]) * ((k : ℤ_[p]) + 1)
      = ((N.choose k : ℕ) : ℤ_[p]) * ((N : ℤ_[p]) - k) := by
  have h := congrArg (fun z : ℤ => (z : ℤ_[p])) (OSS.choose_succ_right_int N k)
  push_cast at h
  exact h

lemma cast_add_one_mul_choose (N k : ℕ) :
    ((N : ℤ_[p]) + 1) * ((N.choose k : ℕ) : ℤ_[p])
      = (((N + 1).choose (k + 1) : ℕ) : ℤ_[p]) * ((k : ℤ_[p]) + 1) := by
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (Nat.add_one_mul_choose_eq N k)
  push_cast at h
  exact h

lemma div_of_succ_dvd {n μ : ℕ} (hμ : n + 1 = p * μ) : (n + 1) / p = μ ∧ n / p = μ - 1 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hμ1 : 1 ≤ μ := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · rw [h] at hμ; omega
    · exact h
  refine ⟨by rw [hμ]; exact Nat.mul_div_cancel_left _ hp0, ?_⟩
  have hk : n = p * (μ - 1) + (p - 1) := by
    have : p * μ = p * (μ - 1) + p := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  rw [hk, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega : p - 1 < p), Nat.add_zero]

omit [Fact p.Prime] in
lemma div_of_succ_not_dvd {n : ℕ} (h : ¬ p ∣ n + 1) : (n + 1) / p = n / p := by
  rw [Nat.succ_div]; simp [h]

/-- Lemma 1.1(i) in the form `L = p A`. -/
lemma choose_pred_prod_aux (A : ℕ) (hA : 1 ≤ A) (n : ℕ) :
    (((p * A - 1).choose n : ℕ) : ℤ_[p])
      = (-1) ^ (n - n / p) * (((A - 1).choose (n / p) : ℕ) : ℤ_[p])
        * Pm p ((p * A : ℕ) : ℤ_[p]) n := by
  have hp : p.Prime := Fact.out
  have hpA : 1 ≤ p * A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hcL : (((p * A - 1 : ℕ)) : ℤ_[p]) = ((p * A : ℕ) : ℤ_[p]) - 1 := by
    rw [Nat.cast_sub hpA, Nat.cast_one]
  have hcA : (((A - 1 : ℕ)) : ℤ_[p]) = (A : ℤ_[p]) - 1 := by rw [Nat.cast_sub hA, Nat.cast_one]
  have hPLe : ((p * A : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * A := by push_cast; ring
  set PL := ((p * A : ℕ) : ℤ_[p]) with hPL
  induction n with
  | zero => simp [Pm]
  | succ n ih =>
    have hc := cast_choose_succ_right p (p * A - 1) n
    rw [hcL] at hc
    rw [Pm_succ]
    set C0 := (((p * A - 1).choose n : ℕ) : ℤ_[p]) with hC0
    set C1 := (((p * A - 1).choose (n + 1) : ℕ) : ℤ_[p]) with hC1
    set Pn := Pm p PL n with hPn
    by_cases hdv : p ∣ (n + 1)
    · obtain ⟨μ, hμ⟩ := hdv
      obtain ⟨hd1, hd0⟩ := div_of_succ_dvd p hμ
      have hμ1 : 1 ≤ μ := by
        rcases Nat.eq_zero_or_pos μ with h | h
        · rw [h] at hμ; omega
        · exact h
      rw [inv_eq_zero_of_dvd p ⟨μ, hμ⟩, mul_zero, sub_zero, mul_one, hd1,
        show n + 1 - μ = n - (μ - 1) by omega]
      rw [hd0] at ih
      have hd := cast_choose_succ_right p (A - 1) (μ - 1)
      rw [hcA, show μ - 1 + 1 = μ by omega, Nat.cast_sub hμ1, Nat.cast_one] at hd
      set D0 := (((A - 1).choose (μ - 1) : ℕ) : ℤ_[p]) with hD0
      set D1 := (((A - 1).choose μ : ℕ) : ℤ_[p]) with hD1
      set σ := ((-1 : ℤ_[p]) ^ (n - (μ - 1))) with hσ
      have hn1 : (n : ℤ_[p]) + 1 = (p : ℤ_[p]) * μ := by exact_mod_cast hμ
      apply mul_right_cancel₀ (Nat.cast_add_one_ne_zero (R := ℤ_[p]) n)
      linear_combination hc + (PL - 1 - n) * ih
        + σ * Pn * (-(p : ℤ_[p]) * hd + D0 * hPLe - (D0 + D1) * hn1)
    · rw [div_of_succ_not_dvd p hdv, show n + 1 - n / p = (n - n / p) + 1 by
        have := Nat.div_le_self n p; omega, pow_succ]
      have hu := mul_inv_nat p hdv
      have hcast : (((n + 1 : ℕ)) : ℤ_[p]) = (n : ℤ_[p]) + 1 := by push_cast; ring
      rw [hcast] at hu ⊢
      set I := Ring.inverse ((n : ℤ_[p]) + 1) with hI
      set D := (((A - 1).choose (n / p) : ℕ) : ℤ_[p]) with hD
      set σ := ((-1 : ℤ_[p]) ^ (n - n / p)) with hσ
      linear_combination (-C1 - σ * D * Pn) * hu + I * hc + (PL - 1 - n) * I * ih

/-- Lemma 1.1(i) with `-m`, in the form `L = p A`. -/
lemma choose_add_prod_aux (A n : ℕ) :
    (((p * A + n).choose n : ℕ) : ℤ_[p])
      = (((A + n / p).choose (n / p) : ℕ) : ℤ_[p]) * Pp p ((p * A : ℕ) : ℤ_[p]) n := by
  have hPLe : ((p * A : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * A := by push_cast; ring
  set PL := ((p * A : ℕ) : ℤ_[p]) with hPL
  induction n with
  | zero => simp [Pp]
  | succ n ih =>
    have hc := cast_add_one_mul_choose p (p * A + n) n
    push_cast at hc
    rw [Pp_succ, ← Nat.add_assoc]
    set C0 := (((p * A + n).choose n : ℕ) : ℤ_[p]) with hC0
    set C1 := (((p * A + n + 1).choose (n + 1) : ℕ) : ℤ_[p]) with hC1
    set Pn := Pp p PL n with hPn
    by_cases hdv : p ∣ (n + 1)
    · obtain ⟨μ, hμ⟩ := hdv
      obtain ⟨hd1, hd0⟩ := div_of_succ_dvd p hμ
      have hμ1 : 1 ≤ μ := by
        rcases Nat.eq_zero_or_pos μ with h | h
        · rw [h] at hμ; omega
        · exact h
      rw [inv_eq_zero_of_dvd p ⟨μ, hμ⟩, mul_zero, add_zero, mul_one, hd1]
      rw [hd0] at ih
      have hd := cast_add_one_mul_choose p (A + (μ - 1)) (μ - 1)
      rw [show A + (μ - 1) + 1 = A + μ by omega, show μ - 1 + 1 = μ by omega] at hd
      rw [Nat.cast_add (A) (μ - 1), Nat.cast_sub hμ1, Nat.cast_one] at hd
      set D0 := (((A + (μ - 1)).choose (μ - 1) : ℕ) : ℤ_[p]) with hD0
      set D1 := (((A + μ).choose μ : ℕ) : ℤ_[p]) with hD1
      have hn1 : (n : ℤ_[p]) + 1 = (p : ℤ_[p]) * μ := by exact_mod_cast hμ
      apply mul_right_cancel₀ (Nat.cast_add_one_ne_zero (R := ℤ_[p]) n)
      linear_combination -hc + ((p : ℤ_[p]) * A + n + 1) * ih
        + Pn * ((p : ℤ_[p]) * hd + (D0 - D1) * hn1)
    · rw [div_of_succ_not_dvd p hdv]
      have hu := mul_inv_nat p hdv
      have hcast : (((n + 1 : ℕ)) : ℤ_[p]) = (n : ℤ_[p]) + 1 := by push_cast; ring
      rw [hcast] at hu ⊢
      set I := Ring.inverse ((n : ℤ_[p]) + 1) with hI
      set D := (((A + n / p).choose (n / p) : ℕ) : ℤ_[p]) with hD
      linear_combination (-C1 + D * Pn) * hu - I * hc + ((p : ℤ_[p]) * A + n + 1) * I * ih
        - D * Pn * I * hPLe

/-- Lemma 1.1(ii) with `-m`, in the form `L = p A`, `n = p μ`. -/
lemma choose_add_pred_prod_aux (A μ : ℕ) :
    (((p * A + p * μ - 1).choose (p * μ) : ℕ) : ℤ_[p])
      = (((A + μ - 1).choose μ : ℕ) : ℤ_[p]) * Pp p ((p * A : ℕ) : ℤ_[p]) (p * μ) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  rcases Nat.eq_zero_or_pos μ with rfl | hμ
  · simp [Pp]
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 1 := ⟨μ - 1, by omega⟩
  have hpμ : 1 ≤ p * (ν + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hdiv : (p * (ν + 1) - 1) / p = ν := by
    have := (div_of_succ_dvd p (show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega)).2
    rw [this]; omega
  have haux := choose_add_prod_aux p A (p * (ν + 1) - 1)
  rw [hdiv] at haux
  have hPp : Pp p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1))
      = Pp p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1) := by
    have h := Pp_succ_of_dvd p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1)
      (by rw [show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega]; exact dvd_mul_right _ _)
    rwa [show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega] at h
  -- ℕ identities
  have h1 : (p * A + p * (ν + 1) - 1).choose (p * (ν + 1)) * (p * (ν + 1))
      = (p * A + (p * (ν + 1) - 1)).choose (p * (ν + 1) - 1) * (p * A) := by
    have h := Nat.choose_succ_right_eq (p * A + p * (ν + 1) - 1) (p * (ν + 1) - 1)
    rw [show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega,
      show p * A + p * (ν + 1) - 1 - (p * (ν + 1) - 1) = p * A by omega,
      show p * A + p * (ν + 1) - 1 = p * A + (p * (ν + 1) - 1) by omega] at h
    rw [show p * A + p * (ν + 1) - 1 = p * A + (p * (ν + 1) - 1) by omega]
    exact h
  have h2 : (A + ν).choose (ν + 1) * (ν + 1) = (A + ν).choose ν * A := by
    have h := Nat.choose_succ_right_eq (A + ν) ν
    rwa [show A + ν - ν = A by omega] at h
  rw [show A + (ν + 1) - 1 = A + ν by omega, hPp]
  have h1' := congrArg (Nat.cast : ℕ → ℤ_[p]) h1
  have h2' := congrArg (Nat.cast : ℕ → ℤ_[p]) h2
  push_cast at h1' h2'
  have hne : ((p : ℤ_[p]) * ((ν : ℤ_[p]) + 1)) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hp.ne_zero
    · exact Nat.cast_add_one_ne_zero ν
  apply mul_right_cancel₀ hne
  set X := (((p * A + p * (ν + 1) - 1).choose (p * (ν + 1)) : ℕ) : ℤ_[p]) with hX
  set Y := (((p * A + (p * (ν + 1) - 1)).choose (p * (ν + 1) - 1) : ℕ) : ℤ_[p]) with hY
  set P := Pp p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1) with hP
  set D := (((A + ν).choose ν : ℕ) : ℤ_[p]) with hD
  set D1 := (((A + ν).choose (ν + 1) : ℕ) : ℤ_[p]) with hD1
  linear_combination h1' + (p : ℤ_[p]) * A * haux - (p : ℤ_[p]) * P * h2'

/-- Lemma 1.1(ii), in the form `L = p A`, `n = p μ`. -/
lemma choose_mul_prod_aux (hp2 : p ≠ 2) (A μ : ℕ) (hA : 1 ≤ A) :
    (((p * A).choose (p * μ) : ℕ) : ℤ_[p])
      = ((A.choose μ : ℕ) : ℤ_[p]) * Pm p ((p * A : ℕ) : ℤ_[p]) (p * μ) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  rcases Nat.eq_zero_or_pos μ with rfl | hμ
  · simp [Pm]
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 1 := ⟨μ - 1, by omega⟩
  have hpμ : 1 ≤ p * (ν + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hpA : 1 ≤ p * A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hdiv : (p * (ν + 1) - 1) / p = ν := by
    have := (div_of_succ_dvd p (show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega)).2
    rw [this]; omega
  have haux := choose_pred_prod_aux p A hA (p * (ν + 1) - 1)
  rw [hdiv] at haux
  have hev : Even (p * (ν + 1) - 1 - ν) := by
    have e : p * (ν + 1) - 1 - ν = (p - 1) * (ν + 1) := by
      rw [Nat.sub_mul, one_mul]; omega
    rw [e]; exact (hp.even_sub_one hp2).mul_right _
  rw [hev.neg_one_pow, one_mul] at haux
  have hPm : Pm p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1))
      = Pm p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1) := by
    have h := Pm_succ_of_dvd p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1)
      (by rw [show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega]; exact dvd_mul_right _ _)
    rwa [show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega] at h
  have h1 : (p * A - 1 + 1) * (p * A - 1).choose (p * (ν + 1) - 1)
      = (p * A - 1 + 1).choose (p * (ν + 1) - 1 + 1) * (p * (ν + 1) - 1 + 1) :=
    Nat.add_one_mul_choose_eq _ _
  rw [show p * A - 1 + 1 = p * A by omega, show p * (ν + 1) - 1 + 1 = p * (ν + 1) by omega] at h1
  have h2 : (A - 1 + 1) * (A - 1).choose ν = (A - 1 + 1).choose (ν + 1) * (ν + 1) :=
    Nat.add_one_mul_choose_eq _ _
  rw [show A - 1 + 1 = A by omega] at h2
  rw [hPm]
  have h1' := congrArg (Nat.cast : ℕ → ℤ_[p]) h1
  have h2' := congrArg (Nat.cast : ℕ → ℤ_[p]) h2
  push_cast at h1' h2'
  have hne : ((p : ℤ_[p]) * ((ν : ℤ_[p]) + 1)) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hp.ne_zero
    · exact Nat.cast_add_one_ne_zero ν
  apply mul_right_cancel₀ hne
  set X := (((p * A).choose (p * (ν + 1)) : ℕ) : ℤ_[p]) with hX
  set Y := (((p * A - 1).choose (p * (ν + 1) - 1) : ℕ) : ℤ_[p]) with hY
  set P := Pm p ((p * A : ℕ) : ℤ_[p]) (p * (ν + 1) - 1) with hP
  set D := (((A - 1).choose ν : ℕ) : ℤ_[p]) with hD
  set D1 := ((A.choose (ν + 1) : ℕ) : ℤ_[p]) with hD1
  linear_combination -h1' + (p : ℤ_[p]) * A * haux + (p : ℤ_[p]) * P * h2'

omit [Fact p.Prime] in
lemma mul_pow_pred (m s : ℕ) (hs : 1 ≤ s) : m * p ^ s = p * (m * p ^ (s - 1)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]; ring

/-- Lemma 1.1(i): `C(L-1, n) = (-1)^(n - [n/p]) C(L′-1, [n/p]) P_n`. -/
theorem choose_pred_prod (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (((m * p ^ s - 1).choose n : ℕ) : ℤ_[p])
      = (-1) ^ (n - n / p) * (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p])
        * Pm p ((m * p ^ s : ℕ) : ℤ_[p]) n := by
  have hA : 1 ≤ m * p ^ (s - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  rw [mul_pow_pred p m s hs]
  exact choose_pred_prod_aux p _ hA n

/-- Lemma 1.1(i) with `-m`: `(-1)^n C(-L-1, n) = C(L+n, n) = C(L′+[n/p], [n/p]) P̄_n`. -/
theorem choose_add_prod (m s n : ℕ) (hs : 1 ≤ s) :
    (((m * p ^ s + n).choose n : ℕ) : ℤ_[p])
      = (((m * p ^ (s - 1) + n / p).choose (n / p) : ℕ) : ℤ_[p])
        * Pp p ((m * p ^ s : ℕ) : ℤ_[p]) n := by
  rw [mul_pow_pred p m s hs]
  exact choose_add_prod_aux p _ n

/-- Lemma 1.1(ii): for `p ∣ n`, `C(L, n) = C(L′, n/p) P_n` (`p` odd). -/
theorem choose_mul_prod (hp2 : p ≠ 2) (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hn : p ∣ n) :
    (((m * p ^ s).choose n : ℕ) : ℤ_[p])
      = (((m * p ^ (s - 1)).choose (n / p) : ℕ) : ℤ_[p]) * Pm p ((m * p ^ s : ℕ) : ℤ_[p]) n := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hA : 1 ≤ m * p ^ (s - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  obtain ⟨μ, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left μ hp0, mul_pow_pred p m s hs]
  exact choose_mul_prod_aux p hp2 _ μ hA

/-- Lemma 1.1(ii) with `-m`: for `p ∣ n`, `(-1)^n C(-L, n) = C(L+n-1, n) = C(L′+n/p-1, n/p) P̄_n`. -/
theorem choose_add_pred_prod (m s n : ℕ) (hs : 1 ≤ s) (hn : p ∣ n) :
    (((m * p ^ s + n - 1).choose n : ℕ) : ℤ_[p])
      = (((m * p ^ (s - 1) + n / p - 1).choose (n / p) : ℕ) : ℤ_[p])
        * Pp p ((m * p ^ s : ℕ) : ℤ_[p]) n := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨μ, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left μ hp0, mul_pow_pred p m s hs]
  exact choose_add_pred_prod_aux p _ μ

/- ### Lemma 1.2 (congruences mod `p^s`) -/

lemma Pm_sub_one_dvd (L : ℤ_[p]) (s x : ℕ) (hL : (p : ℤ_[p]) ^ s ∣ L) :
    (p : ℤ_[p]) ^ s ∣ Pm p L x - 1 := by
  have h := Epoch361883.dvd_prod_sub_prod (range (x + 1)) ((p : ℤ_[p]) ^ s)
    (fun k => 1 - L * Ring.inverse (k : ℤ_[p])) (fun _ => 1)
    (fun k _ => by rw [sub_sub_cancel_left]; exact (hL.mul_right _).neg_right)
  rwa [Finset.prod_const_one] at h

lemma Pp_sub_one_dvd (L : ℤ_[p]) (s x : ℕ) (hL : (p : ℤ_[p]) ^ s ∣ L) :
    (p : ℤ_[p]) ^ s ∣ Pp p L x - 1 := by
  have h := Epoch361883.dvd_prod_sub_prod (range (x + 1)) ((p : ℤ_[p]) ^ s)
    (fun k => 1 + L * Ring.inverse (k : ℤ_[p])) (fun _ => 1)
    (fun k _ => by rw [add_sub_cancel_left]; exact hL.mul_right _)
  rwa [Finset.prod_const_one] at h

lemma ppow_dvd_cast (m s : ℕ) : (p : ℤ_[p]) ^ s ∣ ((m * p ^ s : ℕ) : ℤ_[p]) :=
  ⟨m, by push_cast; ring⟩

omit [Fact p.Prime] in
lemma neg_one_pow_mul_sub {R : Type*} [CommRing R] (n q : ℕ) (h : q ≤ n) :
    (-1 : R) ^ n * (-1) ^ (n - q) = (-1) ^ q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, mul_one]

/-- Lemma 1.2(a): `(-1)^n C(m p^s - 1, n) ≡ (-1)^[n/p] C(m p^(s-1) - 1, [n/p])`. -/
theorem cong_pred (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (-1) ^ n * (((m * p ^ s - 1).choose n : ℕ) : ℤ_[p])
      - (-1) ^ (n / p) * (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p]) := by
  rw [choose_pred_prod p m s n hm hs]
  have hP := Pm_sub_one_dvd p ((m * p ^ s : ℕ) : ℤ_[p]) s n (ppow_dvd_cast p m s)
  have hsg := neg_one_pow_mul_sub (R := ℤ_[p]) n (n / p) (Nat.div_le_self n p)
  set D := (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p])
  set P := Pm p ((m * p ^ s : ℕ) : ℤ_[p]) n
  have e : (-1 : ℤ_[p]) ^ n * ((-1) ^ (n - n / p) * D * P) - (-1) ^ (n / p) * D
      = (-1) ^ (n / p) * D * (P - 1) := by linear_combination (D * P) * hsg
  rw [e]; exact hP.mul_left _

/-- Lemma 1.2(a) with `-m`: `C(m p^s + n, n) ≡ C(m p^(s-1) + [n/p], [n/p])`. -/
theorem cong_add (m s n : ℕ) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s + n).choose n : ℕ) : ℤ_[p])
      - (((m * p ^ (s - 1) + n / p).choose (n / p) : ℕ) : ℤ_[p]) := by
  rw [choose_add_prod p m s n hs]
  have hP := Pp_sub_one_dvd p ((m * p ^ s : ℕ) : ℤ_[p]) s n (ppow_dvd_cast p m s)
  rw [show ∀ D P : ℤ_[p], D * P - D = D * (P - 1) from fun D P => by ring]
  exact hP.mul_left _

/-- Lemma 1.2(b): `C(m p^s, p n) ≡ C(m p^(s-1), n)` (`p` odd). -/
theorem cong_mul (hp2 : p ≠ 2) (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s).choose (p * n) : ℕ) : ℤ_[p])
      - (((m * p ^ (s - 1)).choose n : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [choose_mul_prod p hp2 m s (p * n) hm hs (dvd_mul_right p n), Nat.mul_div_cancel_left n hp0]
  have hP := Pm_sub_one_dvd p ((m * p ^ s : ℕ) : ℤ_[p]) s (p * n) (ppow_dvd_cast p m s)
  rw [show ∀ D P : ℤ_[p], D * P - D = D * (P - 1) from fun D P => by ring]
  exact hP.mul_left _

/-- Lemma 1.2(b) with `-m`: `C(m p^s + p n - 1, p n) ≡ C(m p^(s-1) + n - 1, n)`. -/
theorem cong_add_pred (m s n : ℕ) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s + p * n - 1).choose (p * n) : ℕ) : ℤ_[p])
      - (((m * p ^ (s - 1) + n - 1).choose n : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [choose_add_pred_prod p m s (p * n) hs (dvd_mul_right p n), Nat.mul_div_cancel_left n hp0]
  have hP := Pp_sub_one_dvd p ((m * p ^ s : ℕ) : ℤ_[p]) s (p * n) (ppow_dvd_cast p m s)
  rw [show ∀ D P : ℤ_[p], D * P - D = D * (P - 1) from fun D P => by ring]
  exact hP.mul_left _

/-- Consequence of Lemma 1.2(a): `C(m p^s - 1, n)² ≡ C(m p^(s-1) - 1, [n/p])²`. -/
theorem cong_sq_pred (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s - 1).choose n : ℕ) : ℤ_[p]) ^ 2
      - (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p]) ^ 2 := by
  rw [choose_pred_prod p m s n hm hs]
  have hP := Pm_sub_one_dvd p ((m * p ^ s : ℕ) : ℤ_[p]) s n (ppow_dvd_cast p m s)
  have hsq : ((-1 : ℤ_[p]) ^ (n - n / p)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set D := (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p])
  set P := Pm p ((m * p ^ s : ℕ) : ℤ_[p]) n
  have e : ((-1 : ℤ_[p]) ^ (n - n / p) * D * P) ^ 2 - D ^ 2 = D ^ 2 * (P + 1) * (P - 1) := by
    linear_combination (D ^ 2 * P ^ 2) * hsq
  rw [e]; exact hP.mul_left _

/-- Consequence of Lemma 1.2(a), `p ∤ n`:
`(-1)^(n-1) C(m p^s - 1, n-1) ≡ (-1)^[n/p] C(m p^(s-1) - 1, [n/p])`. -/
theorem cong_pred_pred (m s n : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hn : ¬ p ∣ n) :
    (p : ℤ_[p]) ^ s ∣ (-1) ^ (n - 1) * (((m * p ^ s - 1).choose (n - 1) : ℕ) : ℤ_[p])
      - (-1) ^ (n / p) * (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p]) := by
  have h := cong_pred p m s (n - 1) hm hs
  rwa [OSS.pred_div_eq p n hn] at h

/-- Consequence of Lemma 1.2(a) with `-m`, `p ∤ n`:
`(-1)^(n-1) C(-L-1, n-1) = C(L+n-1, n-1) ≡ C(L′+[n/p], [n/p])`. -/
theorem cong_add_pred_pred (m s n : ℕ) (hs : 1 ≤ s) (hn : ¬ p ∣ n) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s + n - 1).choose (n - 1) : ℕ) : ℤ_[p])
      - (((m * p ^ (s - 1) + n / p).choose (n / p) : ℕ) : ℤ_[p]) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  have h := cong_add p m s (n - 1) hs
  rw [OSS.pred_div_eq p n hn] at h
  rwa [show m * p ^ s + n - 1 = m * p ^ s + (n - 1) by omega]

/- ### Lemma 1.3 (first- and second-order expansion) -/

omit [Fact p.Prime] in
theorem prod_fo {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (L : R) (w : ι → R) :
    L ^ 2 ∣ ∏ i ∈ s, (1 + L * w i) - 1 - L * ∑ i ∈ s, w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    obtain ⟨c, hc⟩ := ih
    set X := ∏ i ∈ s, (1 + L * w i) with hX
    set W := ∑ i ∈ s, w i with hW
    have hX' : X = 1 + L * W + L ^ 2 * c := by linear_combination hc
    rw [hX']
    exact ⟨c + w a * L * c + w a * W, by ring⟩

omit [Fact p.Prime] in
theorem prod_so {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (L : R) (w : ι → R) :
    L ^ 3 ∣ 2 * (∏ i ∈ s, (1 + L * w i) - 1 - L * ∑ i ∈ s, w i)
      - L ^ 2 * ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨c, hc⟩ := prod_fo s L w
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨d, hd⟩ := ih
    set X := ∏ i ∈ s, (1 + L * w i) with hX
    set W := ∑ i ∈ s, w i with hW
    set Q := ∑ i ∈ s, w i ^ 2 with hQ
    have hX' : X = 1 + L * W + L ^ 2 * c := by linear_combination hc
    rw [hX'] at hd ⊢
    exact ⟨d + 2 * w a * c, by linear_combination hd⟩

omit [Fact p.Prime] in
theorem fo_mul {R : Type*} [CommRing R] {L E F e f : R}
    (hE : L ^ 2 ∣ E - 1 - L * e) (hF : L ^ 2 ∣ F - 1 - L * f) :
    L ^ 2 ∣ E * F - 1 - L * (e + f) := by
  obtain ⟨c, hc⟩ := hE
  obtain ⟨d, hd⟩ := hF
  exact ⟨e * f + c + d + L * (e * d + f * c) + L ^ 2 * c * d, by
    linear_combination F * hc + (1 + L * e + L ^ 2 * c) * hd⟩

omit [Fact p.Prime] in
theorem so_mul {R : Type*} [CommRing R] {L E F e f q r : R}
    (hE1 : L ^ 2 ∣ E - 1 - L * e) (hF1 : L ^ 2 ∣ F - 1 - L * f)
    (hE : L ^ 3 ∣ 2 * (E - 1 - L * e) - L ^ 2 * (e ^ 2 - q))
    (hF : L ^ 3 ∣ 2 * (F - 1 - L * f) - L ^ 2 * (f ^ 2 - r)) :
    L ^ 3 ∣ 2 * (E * F - 1 - L * (e + f)) - L ^ 2 * ((e + f) ^ 2 - (q + r)) := by
  obtain ⟨c, hc⟩ := hE1
  obtain ⟨d, hd⟩ := hF1
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hF
  exact ⟨x + y + 2 * (e * d + f * c) + 2 * L * c * d, by
    linear_combination 2 * (F - 1) * hc + 2 * (L * e + L ^ 2 * c) * hd + hx + hy⟩

omit [Fact p.Prime] in
theorem fo_pow {R : Type*} [CommRing R] {L E e : R} (h : L ^ 2 ∣ E - 1 - L * e) (a : ℕ) :
    L ^ 2 ∣ E ^ a - 1 - L * ((a : R) * e) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ E a, show ((a + 1 : ℕ) : R) * e = (a : R) * e + e by push_cast; ring]
    exact fo_mul ih h

omit [Fact p.Prime] in
theorem so_pow {R : Type*} [CommRing R] {L E e q : R} (h1 : L ^ 2 ∣ E - 1 - L * e)
    (h : L ^ 3 ∣ 2 * (E - 1 - L * e) - L ^ 2 * (e ^ 2 - q)) (a : ℕ) :
    L ^ 3 ∣ 2 * (E ^ a - 1 - L * ((a : R) * e)) - L ^ 2 * (((a : R) * e) ^ 2 - (a : R) * q) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ E a, show ((a + 1 : ℕ) : R) * e = (a : R) * e + e by push_cast; ring,
      show ((a + 1 : ℕ) : R) * q = (a : R) * q + q by push_cast; ring]
    exact so_mul (fo_pow h1 a) h1 ih h

lemma Pm_eq (L : ℤ_[p]) (x : ℕ) :
    Pm p L x = ∏ k ∈ range (x + 1), (1 + L * (-Ring.inverse (k : ℤ_[p]))) := by
  unfold Pm; apply Finset.prod_congr rfl; intro k _; ring

lemma neg_H_eq (x : ℕ) : -H p x = ∑ k ∈ range (x + 1), -Ring.inverse (k : ℤ_[p]) := by
  unfold H; rw [Finset.sum_neg_distrib]

lemma S2_eq_neg (x : ℕ) : S p 2 x = ∑ k ∈ range (x + 1), (-Ring.inverse (k : ℤ_[p])) ^ 2 := by
  unfold S; apply Finset.sum_congr rfl; intro k _; ring

theorem Pm_fo (L : ℤ_[p]) (x : ℕ) : L ^ 2 ∣ Pm p L x - 1 - L * (-H p x) := by
  rw [Pm_eq, neg_H_eq]
  exact prod_fo (range (x + 1)) L (fun k => -Ring.inverse (k : ℤ_[p]))

theorem Pp_fo (L : ℤ_[p]) (x : ℕ) : L ^ 2 ∣ Pp p L x - 1 - L * H p x := by
  unfold Pp H
  exact prod_fo (range (x + 1)) L (fun k => Ring.inverse (k : ℤ_[p]))

theorem Pm_so (L : ℤ_[p]) (x : ℕ) :
    L ^ 3 ∣ 2 * (Pm p L x - 1 - L * (-H p x)) - L ^ 2 * ((-H p x) ^ 2 - S p 2 x) := by
  rw [Pm_eq, neg_H_eq, S2_eq_neg]
  exact prod_so (range (x + 1)) L (fun k => -Ring.inverse (k : ℤ_[p]))

theorem Pp_so (L : ℤ_[p]) (x : ℕ) :
    L ^ 3 ∣ 2 * (Pp p L x - 1 - L * H p x) - L ^ 2 * (H p x ^ 2 - S p 2 x) := by
  unfold Pp H S
  exact prod_so (range (x + 1)) L (fun k => Ring.inverse (k : ℤ_[p]))

/-- **Lemma 1.3.** For `E = Π_i P_{x_i}^{a_i} P̄_{y_i}^{b_i}`:
`E ≡ 1 + L e₁ (mod L²)` and `2(E - 1 - L e₁) ≡ L² (e₁² - Σ_i (a_i S₂(x_i) + b_i S₂(y_i))) (mod L³)`,
with `e₁ = Σ_i (b_i H′_{y_i} - a_i H′_{x_i})`; i.e. `e₂ = ½ e₁² - ½ Σ_i (a_i S₂(x_i) + b_i S₂(y_i))`. -/
theorem lemma13 (L : ℤ_[p]) {ι : Type*} (s : Finset ι) (a b x y : ι → ℕ) :
    L ^ 2 ∣ (∏ i ∈ s, Pm p L (x i) ^ a i * Pp p L (y i) ^ b i) - 1
        - L * (∑ i ∈ s, ((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i))) ∧
    L ^ 3 ∣ 2 * ((∏ i ∈ s, Pm p L (x i) ^ a i * Pp p L (y i) ^ b i) - 1
        - L * (∑ i ∈ s, ((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i))))
      - L ^ 2 * ((∑ i ∈ s, ((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i))) ^ 2
          - ∑ i ∈ s, ((a i : ℤ_[p]) * S p 2 (x i) + (b i : ℤ_[p]) * S p 2 (y i))) := by
  classical
  have key : ∀ i, L ^ 2 ∣ Pm p L (x i) ^ a i * Pp p L (y i) ^ b i - 1
        - L * ((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i)) ∧
      L ^ 3 ∣ 2 * (Pm p L (x i) ^ a i * Pp p L (y i) ^ b i - 1
        - L * ((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i)))
        - L ^ 2 * (((b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i)) ^ 2
          - ((a i : ℤ_[p]) * S p 2 (x i) + (b i : ℤ_[p]) * S p 2 (y i))) := by
    intro i
    have h1 := fo_pow (Pm_fo p L (x i)) (a i)
    have h2 := fo_pow (Pp_fo p L (y i)) (b i)
    have h3 := so_pow (Pm_fo p L (x i)) (Pm_so p L (x i)) (a i)
    have h4 := so_pow (Pp_fo p L (y i)) (Pp_so p L (y i)) (b i)
    rw [show (b i : ℤ_[p]) * H p (y i) - (a i : ℤ_[p]) * H p (x i)
      = (a i : ℤ_[p]) * (-H p (x i)) + (b i : ℤ_[p]) * H p (y i) by ring]
    exact ⟨fo_mul h1 h2, so_mul h1 h2 h3 h4⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    exact ⟨fo_mul (key j).1 ih.1, so_mul (key j).1 ih.1 (key j).2 ih.2⟩

end prod

end ShiftLib
