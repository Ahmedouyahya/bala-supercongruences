/-
Parts of this file are taken from the benchmark file statements/lean-targets/364175_1518df7a.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions and the statement are copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import Mathlib
import BalaProofs.BlockProduct
import BalaProofs.FactorialSplit
import BalaProofs.FloorCounting
import BalaProofs.GammaShift

/-!
# A364175: integrality (Radcliffe) and Bala's supercongruence `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))`

Formalisation of `notes/A364175-A364178-factorial-ratio-towers.md` for A364175, parallel to
`BalaProofs/A364178.lean`.

* integer form: `a(n) = Num175 n / Den175 n` with `Num175 n = 3^n (6n)!` and
  `Den175 n = (3n)! (2n)! ∏_{j=1}^{n} (2n + 3j)` (from `Γ(1 + 2n/3)/Γ(1 + 5n/3) = 3^n / ∏ (2n + 3j)`);
* integrality (Theorem 1 of the note, Radcliffe 2026): for `3 ∣ n` the value is the Vasyunin ratio
  `(18m)!(2m)!/((9m)!(6m)!(5m)!)`; for `3 ∤ n` the count of `j ≤ n` with `q^i ∣ 2n + 3j` is
  controlled by `FloorCounting` (`q ≠ 3`), and vanishes for `q = 3`;
* the tower (Theorem 3): with `X = n p^(r-1)`,
  `B(pX) · U(3pX) U(2pX) L(pX) = 3^(pX−X) · U(6pX) · B(X)` in `ℕ`, and in `ZMod (p^(3r))`
  `U(c pX) = W^(cn)` (Lemma A), `L(pX) = 3^(pX−X) W^n` (Lemma B).
-/

open Finset

namespace Bala

/-- the numerator `3^n (6n)!` -/
def Num175 (n : ℕ) : ℕ := 3 ^ n * (6 * n).factorial

/-- the denominator `(3n)! (2n)! ∏_{j=1}^{n} (2n + 3j)` -/
def Den175 (n : ℕ) : ℕ := (3 * n).factorial * (2 * n).factorial * ∏ j ∈ Icc 1 n, (2 * n + 3 * j)

/-- the linear-form product over the units, `L(pX) = ∏_{j < pX, p ∤ j} (2pX + 3j)` -/
def L175 (p X : ℕ) : ℕ :=
  ∏ j ∈ (range (p * X)).filter (fun j => ¬ p ∣ j), (2 * (p * X) + 3 * j)

theorem prod_linear175_pos (n : ℕ) : 0 < ∏ j ∈ Icc 1 n, (2 * n + 3 * j) := by
  apply prod_pos
  intro j hj
  simp only [mem_Icc] at hj
  omega

theorem Den175_pos (n : ℕ) : 0 < Den175 n := by
  unfold Den175
  exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (prod_linear175_pos n)

theorem Num175_pos (n : ℕ) : 0 < Num175 n := by
  unfold Num175
  positivity

/-! ### Integrality (Theorem 1 of the note) -/

/-- the Vasyunin ratio `(18m)!(2m)!/((9m)!(6m)!(5m)!)` is an integer -/
theorem vasyunin_a_dvd (m : ℕ) :
    (9 * m).factorial * (6 * m).factorial * (5 * m).factorial
      ∣ (18 * m).factorial * (2 * m).factorial := by
  have hD : (9 * m).factorial * (6 * m).factorial * (5 * m).factorial ≠ 0 := by positivity
  have hN : (18 * m).factorial * (2 * m).factorial ≠ 0 := by positivity
  rw [← Nat.factorization_prime_le_iff_dvd hD hN]
  intro q hq
  have := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  have hL : padicValNat q ((9 * m).factorial * (6 * m).factorial * (5 * m).factorial)
      = padicValNat q (9 * m).factorial + padicValNat q (6 * m).factorial
        + padicValNat q (5 * m).factorial := by
    rw [padicValNat.mul, padicValNat.mul] <;> positivity
  have hR : padicValNat q ((18 * m).factorial * (2 * m).factorial)
      = padicValNat q (18 * m).factorial + padicValNat q (2 * m).factorial := by
    rw [padicValNat.mul] <;> positivity
  rw [hL, hR]
  set b := 18 * m + 1 with hb
  rw [padicValNat_factorial_of_lt q (9 * m) b (by omega),
    padicValNat_factorial_of_lt q (6 * m) b (by omega),
    padicValNat_factorial_of_lt q (5 * m) b (by omega),
    padicValNat_factorial_of_lt q (18 * m) b (by omega),
    padicValNat_factorial_of_lt q (2 * m) b (by omega)]
  have key : ∀ i ∈ Ico 1 b, 9 * m / q ^ i + 6 * m / q ^ i + 5 * m / q ^ i
      ≤ 18 * m / q ^ i + 2 * m / q ^ i := by
    intro i _
    have hQ : 0 < q ^ i := pow_pos hq.pos i
    have hρ : m % q ^ i < q ^ i := Nat.mod_lt m hQ
    have h9 := mul_div_decompose 9 m (q ^ i) hQ
    have h6 := mul_div_decompose 6 m (q ^ i) hQ
    have h5 := mul_div_decompose 5 m (q ^ i) hQ
    have h18 := mul_div_decompose 18 m (q ^ i) hQ
    have h2 := mul_div_decompose 2 m (q ^ i) hQ
    have hfl := floor_ineq_vas_a (q ^ i) (m % q ^ i) hQ hρ
    omega
  have h := sum_le_sum key
  simp only [sum_add_distrib] at h
  omega

/-- `3 ∣ n`, `n = 3m`: `Den175 (3m) · (2m)! = 3^(3m) (9m)!(6m)!(5m)!`,
`Num175 (3m) · (2m)! = 3^(3m) (18m)!(2m)!` -/
theorem den_dvd_num175_three (m : ℕ) : Den175 (3 * m) ∣ Num175 (3 * m) := by
  have hprod : ∏ j ∈ Icc 1 (3 * m), (2 * (3 * m) + 3 * j)
      = 3 ^ (3 * m) * ∏ j ∈ Icc 1 (3 * m), (2 * m + j) := by
    have h : ∀ j ∈ Icc 1 (3 * m), 2 * (3 * m) + 3 * j = 3 * (2 * m + j) := by
      intro j _
      ring
    rw [prod_congr rfl h, prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hfac : (2 * m).factorial * ∏ j ∈ Icc 1 (3 * m), (2 * m + j) = (5 * m).factorial := by
    rw [prod_Icc_one_eq_prod_range]
    have h := Nat.factorial_mul_ascFactorial (2 * m) (3 * m)
    rw [Nat.ascFactorial_eq_prod_range] at h
    rw [show 5 * m = 2 * m + 3 * m by ring, ← h]
    congr 1
    apply prod_congr rfl
    intro i _
    ring
  have hvas := vasyunin_a_dvd m
  have hmpos : 0 < (2 * m).factorial := Nat.factorial_pos _
  apply Nat.dvd_of_mul_dvd_mul_right hmpos
  have e1 : Den175 (3 * m) * (2 * m).factorial
      = 3 ^ (3 * m) * ((9 * m).factorial * (6 * m).factorial * (5 * m).factorial) := by
    unfold Den175
    rw [hprod, show 3 * (3 * m) = 9 * m by ring, show 2 * (3 * m) = 6 * m by ring, ← hfac]
    ring
  have e2 : Num175 (3 * m) * (2 * m).factorial
      = 3 ^ (3 * m) * ((18 * m).factorial * (2 * m).factorial) := by
    unfold Num175
    rw [show 6 * (3 * m) = 18 * m by ring]
    ring
  rw [e1, e2]
  exact mul_dvd_mul_left _ hvas

/-- the termwise Legendre inequality for `3 ∤ n` -/
theorem termwise_a (q i n : ℕ) (hq : q.Prime) (hi : 1 ≤ i) (hn : ¬ 3 ∣ n) :
    3 * n / q ^ i + 2 * n / q ^ i + ((Icc 1 n).filter (fun j => q ^ i ∣ 2 * n + 3 * j)).card
      ≤ 6 * n / q ^ i := by
  have hQ : 0 < q ^ i := pow_pos hq.pos i
  have hρ : n % q ^ i < q ^ i := Nat.mod_lt n hQ
  have h3 := mul_div_decompose 3 n (q ^ i) hQ
  have h2 := mul_div_decompose 2 n (q ^ i) hQ
  have h6 := mul_div_decompose 6 n (q ^ i) hQ
  have hfl := floor_ineq_a (q ^ i) (n % q ^ i) hQ hρ
  have hcount : ((Icc 1 n).filter (fun j => q ^ i ∣ 2 * n + 3 * j)).card
      ≤ n / q ^ i + if q ^ i ≤ 5 * (n % q ^ i) then 1 else 0 := by
    by_cases hq3 : q = 3
    · subst hq3
      have hempty : (Icc 1 n).filter (fun j => 3 ^ i ∣ 2 * n + 3 * j) = ∅ := by
        rw [filter_eq_empty_iff]
        intro j _ hdvd
        have h2 : 3 ∣ 3 ^ i := dvd_pow_self 3 (by omega)
        have h3 : 3 ∣ 2 * n + 3 * j := h2.trans hdvd
        omega
      rw [hempty, card_empty]
      exact Nat.zero_le _
    · have hcop : Nat.Coprime (q ^ i) 3 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_three).mpr hq3)
      have h := card_filter_le_div_add (q ^ i) 3 2 n hQ (by norm_num) hcop
      simp only [Nat.reduceAdd] at h
      exact h
  split_ifs at hfl hcount with hc <;> omega

theorem den_dvd_num175_coprime (n : ℕ) (hn : ¬ 3 ∣ n) : Den175 n ∣ Num175 n := by
  have hden : Den175 n ≠ 0 := (Den175_pos n).ne'
  have hnum : Num175 n ≠ 0 := (Num175_pos n).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hden hnum]
  intro q hq
  have := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  have hprod := (prod_linear175_pos n).ne'
  have hv_den : padicValNat q (Den175 n)
      = padicValNat q (3 * n).factorial + padicValNat q (2 * n).factorial
        + padicValNat q (∏ j ∈ Icc 1 n, (2 * n + 3 * j)) := by
    unfold Den175
    rw [padicValNat.mul _ hprod, padicValNat.mul] <;> positivity
  have hv_num : padicValNat q (Num175 n)
      = padicValNat q (3 ^ n) + padicValNat q (6 * n).factorial := by
    unfold Num175
    rw [padicValNat.mul] <;> positivity
  rw [hv_den, hv_num]
  set b := 6 * n + 1 with hb
  rw [padicValNat_factorial_of_lt q (3 * n) b (by omega),
    padicValNat_factorial_of_lt q (2 * n) b (by omega),
    padicValNat_factorial_of_lt q (6 * n) b (by omega)]
  have hprodv := padicValNat_prod_linear q 2 3 n b (by norm_num) (by linarith)
  rw [hprodv]
  have key : ∀ i ∈ Ico 1 b, 3 * n / q ^ i + 2 * n / q ^ i
      + ((Icc 1 n).filter (fun j => q ^ i ∣ 2 * n + 3 * j)).card ≤ 6 * n / q ^ i := by
    intro i hi
    simp only [mem_Ico] at hi
    exact termwise_a q i n hq hi.1 hn
  have h := sum_le_sum key
  simp only [sum_add_distrib] at h
  omega

/-- **Theorem 1 of the note** (Radcliffe): A364175 is an integer sequence. -/
theorem den_dvd_num175 (n : ℕ) : Den175 n ∣ Num175 n := by
  by_cases h3 : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3
    exact den_dvd_num175_three m
  · exact den_dvd_num175_coprime n h3

/-- the integer value `B175 n = Num175 n / Den175 n` -/
def B175 (n : ℕ) : ℕ := Num175 n / Den175 n

theorem B175_mul_den (n : ℕ) : B175 n * Den175 n = Num175 n :=
  Nat.div_mul_cancel (den_dvd_num175 n)

/-! ### The tower: the exact identity in `ℕ` -/

/-- `B(pX) · U(3pX) U(2pX) L(pX) = 3^(pX−X) · U(6pX) · B(X)` -/
theorem key_identity175 (p X : ℕ) (hp : 0 < p) :
    B175 (p * X) * (U p (3 * (p * X)) * U p (2 * (p * X)) * L175 p X)
      = 3 ^ (p * X - X) * U p (6 * (p * X)) * B175 X := by
  have hXY : X ≤ p * X := Nat.le_mul_of_pos_left X hp
  have hY : 3 ^ (p * X) = 3 ^ (p * X - X) * 3 ^ X := by
    rw [← pow_add, Nat.sub_add_cancel hXY]
  have hf : ∀ c : ℕ, (c * (p * X)).factorial
      = p ^ (c * X) * (c * X).factorial * U p (c * (p * X)) := by
    intro c
    have h := factorial_mul_eq p (c * X) hp
    rwa [show p * (c * X) = c * (p * X) by ring] at h
  have hL := prod_linear_split p X 2 3 hp
  have hNumY : Num175 (p * X)
      = 3 ^ (p * X - X) * p ^ (6 * X) * U p (6 * (p * X)) * Num175 X := by
    unfold Num175
    rw [hf 6, hY]
    ring
  have hDenY : Den175 (p * X)
      = p ^ (6 * X) * Den175 X * (U p (3 * (p * X)) * U p (2 * (p * X)) * L175 p X) := by
    unfold Den175 L175
    rw [hf 3, hf 2, hL]
    ring
  have hpos : 0 < p ^ (6 * X) * Den175 X := Nat.mul_pos (pow_pos hp _) (Den175_pos X)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ (6 * X) * Den175 X
        * (B175 (p * X) * (U p (3 * (p * X)) * U p (2 * (p * X)) * L175 p X))
      = B175 (p * X) * (p ^ (6 * X) * Den175 X
          * (U p (3 * (p * X)) * U p (2 * (p * X)) * L175 p X)) := by ring
    _ = B175 (p * X) * Den175 (p * X) := by rw [hDenY]
    _ = Num175 (p * X) := B175_mul_den (p * X)
    _ = 3 ^ (p * X - X) * p ^ (6 * X) * U p (6 * (p * X)) * Num175 X := hNumY
    _ = 3 ^ (p * X - X) * p ^ (6 * X) * U p (6 * (p * X)) * (B175 X * Den175 X) := by
        rw [B175_mul_den X]
    _ = p ^ (6 * X) * Den175 X * (3 ^ (p * X - X) * U p (6 * (p * X)) * B175 X) := by ring

/-! ### The tower in `ZMod (p^(3r))` -/

theorem B175_congr (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    B175 (n * p ^ r) ≡ B175 (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have : NeZero (p ^ (3 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set X := n * p ^ (r - 1) with hX
  have hpr : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hY : n * p ^ r = p * X := by
    rw [hX, hpr]
    ring
  rw [hY, ← ZMod.natCast_eq_natCast_iff]
  have key := key_identity175 p X hp.pos
  have hcast := congrArg (fun k : ℕ => (k : ZMod (p ^ (3 * r)))) key
  push_cast at hcast
  set W : ZMod (p ^ (3 * r)) :=
    ∏ v ∈ (range (p ^ r)).filter (fun v => ¬ p ∣ v), (v : ZMod (p ^ (3 * r))) with hW
  have hU : ∀ c : ℕ, ((U p (c * (p * X)) : ℕ) : ZMod (p ^ (3 * r))) = W ^ (c * n) := by
    intro c
    unfold U
    push_cast
    have h := prod_units_eq_pow p r (c * n) hp hp5 hr
    rw [show c * n * p ^ r = c * (p * X) by rw [hX, hpr]; ring] at h
    exact h
  have hU1 : ((U p (p * X) : ℕ) : ZMod (p ^ (3 * r))) = W ^ n := by
    have h := hU 1
    rwa [one_mul, one_mul] at h
  have h3unit : IsUnit (3 : ZMod (p ^ (3 * r))) := by
    have hcop : Nat.Coprime 3 (p ^ (3 * r)) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    have := (ZMod.isUnit_iff_coprime 3 (p ^ (3 * r))).mpr hcop
    simpa using this
  have hL : ((L175 p X : ℕ) : ZMod (p ^ (3 * r))) = 3 ^ (p * X - X) * W ^ n := by
    unfold L175
    push_cast
    have h := prod_units_linear p r n hp hp5 hr 3 (2 * (n : ZMod (p ^ (3 * r)))) h3unit
    rw [show n * p ^ r = p * X by rw [hX, hpr]; ring] at h
    have hpX : (p : ZMod (p ^ (3 * r))) * (X : ZMod (p ^ (3 * r)))
        = (n : ZMod (p ^ (3 * r))) * (p : ZMod (p ^ (3 * r))) ^ r := by
      have h' : ((p * X : ℕ) : ZMod (p ^ (3 * r))) = ((n * p ^ r : ℕ) : ZMod (p ^ (3 * r))) := by
        rw [hY]
      push_cast at h'
      exact h'
    have e : ∀ j ∈ (range (p * X)).filter (fun j => ¬ p ∣ j),
        (2 * ((p : ZMod (p ^ (3 * r))) * (X : ZMod (p ^ (3 * r)))) + 3 * (j : ZMod (p ^ (3 * r))))
          = 3 * (j : ZMod (p ^ (3 * r)))
            + 2 * (n : ZMod (p ^ (3 * r))) * (p : ZMod (p ^ (3 * r))) ^ r := by
      intro j _
      linear_combination 2 * hpX
    rw [prod_congr rfl e, h, prod_mul_distrib, prod_const, card_filter_not_dvd_range_mul p X hp.pos]
    congr 1
    have h1 := hU1
    unfold U at h1
    push_cast at h1
    exact h1
  rw [hU 3, hU 2, hU 6, hL] at hcast
  have hunit : IsUnit ((3 : ZMod (p ^ (3 * r))) ^ (p * X - X) * W ^ (6 * n)) :=
    (h3unit.pow _).mul ((isUnit_W p r hp).pow _)
  apply hunit.mul_right_cancel
  calc (B175 (p * X) : ZMod (p ^ (3 * r))) * (3 ^ (p * X - X) * W ^ (6 * n))
      = (B175 (p * X) : ZMod (p ^ (3 * r)))
          * (W ^ (3 * n) * W ^ (2 * n) * (3 ^ (p * X - X) * W ^ n)) := by ring
    _ = 3 ^ (p * X - X) * W ^ (6 * n) * (B175 X : ZMod (p ^ (3 * r))) := hcast
    _ = (B175 X : ZMod (p ^ (3 * r))) * (3 ^ (p * X - X) * W ^ (6 * n)) := by ring

end Bala

/-! ### The benchmark statement (`lean-targets/364175_1518df7a.lean`) -/

open Real

/--
A364175: $a(n) = \frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$.
The fractional factorial $x!$ is defined as $\Gamma(x+1)$.
This sequence is only conjecturally an integer sequence. We round the real-valued result to obtain a natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

namespace Bala

/-- the Γ-quotient of the benchmark equals the integer form -/
theorem val_eq175 (n : ℕ) :
    (Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (2 / 3 * (n : ℝ) + 1)) /
      (Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
        * Real.Gamma (5 / 3 * (n : ℝ) + 1))
      = (Num175 n : ℝ) / (Den175 n : ℝ) := by
  have h6 : Real.Gamma (6 * (n : ℝ) + 1) = ((6 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (6 * n)
    push_cast at h
    exact h
  have h3 : Real.Gamma (3 * (n : ℝ) + 1) = ((3 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (3 * n)
    push_cast at h
    exact h
  have h2 : Real.Gamma (2 * (n : ℝ) + 1) = ((2 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (2 * n)
    push_cast at h
    exact h
  have hx : (0 : ℝ) < 2 / 3 * (n : ℝ) + 1 := by positivity
  have hthird : Real.Gamma (5 / 3 * (n : ℝ) + 1)
      = Real.Gamma (2 / 3 * (n : ℝ) + 1) * ∏ j ∈ range n, (2 / 3 * (n : ℝ) + 1 + j) := by
    rw [← Gamma_add_nat_eq _ hx n]
    congr 1
    ring
  have hP : ∏ j ∈ range n, (2 / 3 * (n : ℝ) + 1 + j)
      = ((∏ j ∈ Icc 1 n, (2 * n + 3 * j) : ℕ) : ℝ) / 3 ^ n := by
    push_cast
    rw [prod_Icc_one_eq_prod_range]
    have h3n : (3 : ℝ) ^ n = ∏ _j ∈ range n, (3 : ℝ) := by
      rw [prod_const, card_range]
    rw [h3n, ← prod_div_distrib]
    apply prod_congr rfl
    intro j _
    push_cast
    ring
  rw [h6, h3, h2, hthird, hP]
  unfold Num175 Den175
  push_cast
  have hG : Real.Gamma (2 / 3 * (n : ℝ) + 1) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hPne : (∏ j ∈ Icc 1 n, (2 * (n : ℝ) + 3 * (j : ℝ))) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro j hj
    simp only [mem_Icc] at hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    positivity
  have hf6 : ((6 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf3 : ((3 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf2 : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3n : (3 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- the benchmark's `a n` is the integer `Num175 n / Den175 n` -/
theorem a_eq_B175 (n : ℕ) : a n = B175 n := by
  have hdvd := den_dvd_num175 n
  have hden : (Den175 n : ℝ) ≠ 0 := by exact_mod_cast (Den175_pos n).ne'
  unfold a B175
  dsimp only
  rw [val_eq175 n, ← Nat.cast_div hdvd hden, round_natCast, Int.toNat_natCast]

end Bala

open Bala in
theorem a_zero : a 0 = 1 := by
  rw [a_eq_B175]
  decide

open Bala in
/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $r$.
Note: The expression $r-1$ is a natural number subtraction, which is safe since $r$ is positive.
-/
theorem oeis_364175_conjecture_0 (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  rw [a_eq_B175, a_eq_B175]
  exact B175_congr p n r hp h_prime_ge_five hr
