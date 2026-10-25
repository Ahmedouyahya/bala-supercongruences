/-
Parts of this file are taken from the benchmark file statements/lean-targets/364178_4c681d65.lean:
Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Changed by the authors of this repository: the definitions and the statement are copied verbatim from that file and a proof is supplied; the import lines differ.
-/
import Mathlib
import BalaProofs.BlockProduct
import BalaProofs.FactorialSplit
import BalaProofs.FloorCounting
import BalaProofs.GammaShift

/-!
# A364178: integrality and Bala's supercongruence `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))`, `p ≥ 5`

Formalisation of `notes/A364175-A364178-factorial-ratio-towers.md` for A364178.

* integer form: `a(n) = Num178 n / Den178 n` with `Num178 n = 2^n (10n)! (3n)!` and
  `Den178 n = (6n)! (5n)! n! ∏_{j=1}^{n} (n + 2j)` (from `Γ(1 + n/2)/Γ(1 + 3n/2) = 2^n / ∏ (n + 2j)`);
* integrality (Theorem 2 of the note): `Den178 n ∣ Num178 n`, by Legendre's formula — for even `n`
  the value is the Vasyunin ratio `(20m)!(6m)!m!/((12m)!(10m)!(3m)!(2m)!)`, for odd `n` the
  count of `j ≤ n` with `q^i ∣ n + 2j` is controlled by `FloorCounting`;
* the tower (Theorem 3): with `X = n p^(r-1)`, Lemma C gives the exact identity
  `B(pX) · U(6pX) U(5pX) U(pX) L(pX) = 2^(pX−X) · U(10pX) U(3pX) · B(X)` in `ℕ`, and in
  `ZMod (p^(3r))` every `U(c pX)` is `W^(cn)` (Lemma A) and `L(pX) = 2^(pX−X) W^n` (Lemma B).
-/

open Finset

namespace Bala

/-- the numerator `2^n (10n)! (3n)!` -/
def Num178 (n : ℕ) : ℕ := 2 ^ n * (10 * n).factorial * (3 * n).factorial

/-- the denominator `(6n)! (5n)! n! ∏_{j=1}^{n} (n + 2j)` -/
def Den178 (n : ℕ) : ℕ :=
  (6 * n).factorial * (5 * n).factorial * n.factorial * ∏ j ∈ Icc 1 n, (n + 2 * j)

/-- the linear-form product over the units, `L(pX) = ∏_{j < pX, p ∤ j} (pX + 2j)` -/
def L178 (p X : ℕ) : ℕ := ∏ j ∈ (range (p * X)).filter (fun j => ¬ p ∣ j), (p * X + 2 * j)

theorem prod_linear_pos (n : ℕ) : 0 < ∏ j ∈ Icc 1 n, (n + 2 * j) := by
  apply prod_pos
  intro j hj
  simp only [mem_Icc] at hj
  omega

theorem Den178_pos (n : ℕ) : 0 < Den178 n := by
  unfold Den178
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    (Nat.factorial_pos _)) (prod_linear_pos n)

theorem Num178_pos (n : ℕ) : 0 < Num178 n := by
  unfold Num178
  positivity

/-! ### Integrality (Theorem 2 of the note) -/

/-- the Vasyunin ratio `(20m)!(6m)!m!/((12m)!(10m)!(3m)!(2m)!)` is an integer (Landau's criterion,
termwise in Legendre's formula) -/
theorem vasyunin_dvd (m : ℕ) :
    (12 * m).factorial * (10 * m).factorial * (2 * m).factorial * (3 * m).factorial
      ∣ (20 * m).factorial * (6 * m).factorial * m.factorial := by
  have hD : (12 * m).factorial * (10 * m).factorial * (2 * m).factorial * (3 * m).factorial ≠ 0 := by
    positivity
  have hN : (20 * m).factorial * (6 * m).factorial * m.factorial ≠ 0 := by positivity
  rw [← Nat.factorization_prime_le_iff_dvd hD hN]
  intro q hq
  have := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  have hL : padicValNat q ((12 * m).factorial * (10 * m).factorial * (2 * m).factorial
        * (3 * m).factorial)
      = padicValNat q (12 * m).factorial + padicValNat q (10 * m).factorial
        + padicValNat q (2 * m).factorial + padicValNat q (3 * m).factorial := by
    rw [padicValNat.mul, padicValNat.mul, padicValNat.mul] <;> positivity
  have hR : padicValNat q ((20 * m).factorial * (6 * m).factorial * m.factorial)
      = padicValNat q (20 * m).factorial + padicValNat q (6 * m).factorial
        + padicValNat q m.factorial := by
    rw [padicValNat.mul, padicValNat.mul] <;> positivity
  rw [hL, hR]
  set b := 20 * m + 1 with hb
  rw [padicValNat_factorial_of_lt q (12 * m) b (by omega),
    padicValNat_factorial_of_lt q (10 * m) b (by omega),
    padicValNat_factorial_of_lt q (2 * m) b (by omega),
    padicValNat_factorial_of_lt q (3 * m) b (by omega),
    padicValNat_factorial_of_lt q (20 * m) b (by omega),
    padicValNat_factorial_of_lt q (6 * m) b (by omega),
    padicValNat_factorial_of_lt q m b (by omega)]
  have key : ∀ i ∈ Ico 1 b, 12 * m / q ^ i + 10 * m / q ^ i + 2 * m / q ^ i + 3 * m / q ^ i
      ≤ 20 * m / q ^ i + 6 * m / q ^ i + m / q ^ i := by
    intro i _
    have hQ : 0 < q ^ i := pow_pos hq.pos i
    have hρ : m % q ^ i < q ^ i := Nat.mod_lt m hQ
    have h12 := mul_div_decompose 12 m (q ^ i) hQ
    have h10 := mul_div_decompose 10 m (q ^ i) hQ
    have h2 := mul_div_decompose 2 m (q ^ i) hQ
    have h3 := mul_div_decompose 3 m (q ^ i) hQ
    have h20 := mul_div_decompose 20 m (q ^ i) hQ
    have h6 := mul_div_decompose 6 m (q ^ i) hQ
    have h1 : m % q ^ i / q ^ i = 0 := Nat.div_eq_of_lt hρ
    have hfl := floor_ineq_vas (q ^ i) (m % q ^ i) hQ hρ
    omega
  have h := sum_le_sum key
  simp only [sum_add_distrib] at h
  omega

/-- even `n = 2m`: `Den178 (2m) · m! = 2^(2m) (12m)!(10m)!(2m)!(3m)!`,
`Num178 (2m) · m! = 2^(2m) (20m)!(6m)! m!` -/
theorem den_dvd_num_even (m : ℕ) : Den178 (2 * m) ∣ Num178 (2 * m) := by
  have hprod : ∏ j ∈ Icc 1 (2 * m), (2 * m + 2 * j) = 2 ^ (2 * m) * ∏ j ∈ Icc 1 (2 * m), (m + j) := by
    have h : ∀ j ∈ Icc 1 (2 * m), 2 * m + 2 * j = 2 * (m + j) := by
      intro j _
      ring
    rw [prod_congr rfl h, prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hfac : m.factorial * ∏ j ∈ Icc 1 (2 * m), (m + j) = (3 * m).factorial := by
    rw [prod_Icc_one_eq_prod_range]
    have h := Nat.factorial_mul_ascFactorial m (2 * m)
    rw [Nat.ascFactorial_eq_prod_range] at h
    rw [show 3 * m = m + 2 * m by ring, ← h]
    congr 1
    apply prod_congr rfl
    intro i _
    ring
  have hvas := vasyunin_dvd m
  have hmpos : 0 < m.factorial := Nat.factorial_pos m
  apply Nat.dvd_of_mul_dvd_mul_right hmpos
  have e1 : Den178 (2 * m) * m.factorial
      = 2 ^ (2 * m) * ((12 * m).factorial * (10 * m).factorial * (2 * m).factorial
          * (3 * m).factorial) := by
    unfold Den178
    rw [hprod, show 6 * (2 * m) = 12 * m by ring, show 5 * (2 * m) = 10 * m by ring, ← hfac]
    ring
  have e2 : Num178 (2 * m) * m.factorial
      = 2 ^ (2 * m) * ((20 * m).factorial * (6 * m).factorial * m.factorial) := by
    unfold Num178
    rw [show 10 * (2 * m) = 20 * m by ring, show 3 * (2 * m) = 6 * m by ring]
    ring
  rw [e1, e2]
  exact mul_dvd_mul_left _ hvas

/-- the termwise Legendre inequality for odd `n` -/
theorem termwise_b (q i n : ℕ) (hq : q.Prime) (hi : 1 ≤ i) (hn : Odd n) :
    6 * n / q ^ i + 5 * n / q ^ i + n / q ^ i
        + ((Icc 1 n).filter (fun j => q ^ i ∣ n + 2 * j)).card
      ≤ 10 * n / q ^ i + 3 * n / q ^ i := by
  have hQ : 0 < q ^ i := pow_pos hq.pos i
  have hρ : n % q ^ i < q ^ i := Nat.mod_lt n hQ
  have h6 := mul_div_decompose 6 n (q ^ i) hQ
  have h5 := mul_div_decompose 5 n (q ^ i) hQ
  have h10 := mul_div_decompose 10 n (q ^ i) hQ
  have h3 := mul_div_decompose 3 n (q ^ i) hQ
  have hfl := floor_ineq_b (q ^ i) (n % q ^ i) hQ hρ
  have hcount : ((Icc 1 n).filter (fun j => q ^ i ∣ n + 2 * j)).card
      ≤ n / q ^ i + if q ^ i ≤ 3 * (n % q ^ i) then 1 else 0 := by
    rcases hq.eq_two_or_odd' with rfl | hodd
    · have hempty : (Icc 1 n).filter (fun j => 2 ^ i ∣ n + 2 * j) = ∅ := by
        rw [filter_eq_empty_iff]
        intro j _ hdvd
        have h2 : 2 ∣ 2 ^ i := dvd_pow_self 2 (by omega)
        have h3 : 2 ∣ n + 2 * j := h2.trans hdvd
        have h4 := Nat.odd_iff.mp hn
        omega
      rw [hempty, card_empty]
      exact Nat.zero_le _
    · have hq2 : q ≠ 2 := by
        rintro rfl
        exact absurd (Nat.odd_iff.mp hodd) (by norm_num)
      have hcop : Nat.Coprime (q ^ i) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
      have h := card_filter_le_div_add (q ^ i) 2 1 n hQ (by norm_num) hcop
      simp only [one_mul, Nat.reduceAdd] at h
      exact h
  split_ifs at hfl hcount with hc <;> omega

theorem den_dvd_num_odd (n : ℕ) (hn : Odd n) : Den178 n ∣ Num178 n := by
  have hden : Den178 n ≠ 0 := (Den178_pos n).ne'
  have hnum : Num178 n ≠ 0 := (Num178_pos n).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hden hnum]
  intro q hq
  have := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  have hprod := (prod_linear_pos n).ne'
  have hv_den : padicValNat q (Den178 n)
      = padicValNat q (6 * n).factorial + padicValNat q (5 * n).factorial
        + padicValNat q n.factorial + padicValNat q (∏ j ∈ Icc 1 n, (n + 2 * j)) := by
    unfold Den178
    rw [padicValNat.mul _ hprod, padicValNat.mul, padicValNat.mul] <;> positivity
  have hv_num : padicValNat q (Num178 n)
      = padicValNat q (2 ^ n) + padicValNat q (10 * n).factorial
        + padicValNat q (3 * n).factorial := by
    unfold Num178
    rw [padicValNat.mul, padicValNat.mul] <;> positivity
  rw [hv_den, hv_num]
  set b := 10 * n + 1 with hb
  rw [padicValNat_factorial_of_lt q (6 * n) b (by omega),
    padicValNat_factorial_of_lt q (5 * n) b (by omega),
    padicValNat_factorial_of_lt q n b (by omega),
    padicValNat_factorial_of_lt q (10 * n) b (by omega),
    padicValNat_factorial_of_lt q (3 * n) b (by omega)]
  have hprodv := padicValNat_prod_linear q 1 2 n b (by norm_num) (by linarith)
  simp only [one_mul] at hprodv
  rw [hprodv]
  have key : ∀ i ∈ Ico 1 b, 6 * n / q ^ i + 5 * n / q ^ i + n / q ^ i
      + ((Icc 1 n).filter (fun j => q ^ i ∣ n + 2 * j)).card ≤ 10 * n / q ^ i + 3 * n / q ^ i := by
    intro i hi
    simp only [mem_Ico] at hi
    exact termwise_b q i n hq hi.1 hn
  have h := sum_le_sum key
  simp only [sum_add_distrib] at h
  omega

/-- **Theorem 2 of the note**: A364178 is an integer sequence. -/
theorem den_dvd_num (n : ℕ) : Den178 n ∣ Num178 n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [show n = 2 * m by omega]
    exact den_dvd_num_even m
  · exact den_dvd_num_odd n ho

/-- the integer value `B178 n = Num178 n / Den178 n` -/
def B178 (n : ℕ) : ℕ := Num178 n / Den178 n

theorem B178_mul_den (n : ℕ) : B178 n * Den178 n = Num178 n :=
  Nat.div_mul_cancel (den_dvd_num n)

/-! ### The tower: the exact identity in `ℕ` -/

/-- `B(pX) · U(6pX) U(5pX) U(pX) L(pX) = 2^(pX−X) · U(10pX) U(3pX) · B(X)` -/
theorem key_identity (p X : ℕ) (hp : 0 < p) :
    B178 (p * X) * (U p (6 * (p * X)) * U p (5 * (p * X)) * U p (p * X) * L178 p X)
      = 2 ^ (p * X - X) * (U p (10 * (p * X)) * U p (3 * (p * X))) * B178 X := by
  have hXY : X ≤ p * X := Nat.le_mul_of_pos_left X hp
  have hY : 2 ^ (p * X) = 2 ^ (p * X - X) * 2 ^ X := by
    rw [← pow_add, Nat.sub_add_cancel hXY]
  have hf : ∀ c : ℕ, (c * (p * X)).factorial
      = p ^ (c * X) * (c * X).factorial * U p (c * (p * X)) := by
    intro c
    have h := factorial_mul_eq p (c * X) hp
    rwa [show p * (c * X) = c * (p * X) by ring] at h
  have hL := prod_linear_split p X 1 2 hp
  simp only [one_mul] at hL
  have hNumY : Num178 (p * X)
      = 2 ^ (p * X - X) * p ^ (13 * X) * (U p (10 * (p * X)) * U p (3 * (p * X))) * Num178 X := by
    unfold Num178
    rw [hf 10, hf 3, hY]
    ring
  have hDenY : Den178 (p * X)
      = p ^ (13 * X) * Den178 X
        * (U p (6 * (p * X)) * U p (5 * (p * X)) * U p (p * X) * L178 p X) := by
    unfold Den178 L178
    rw [hf 6, hf 5, factorial_mul_eq p X hp, hL]
    ring
  have hpos : 0 < p ^ (13 * X) * Den178 X := Nat.mul_pos (pow_pos hp _) (Den178_pos X)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ (13 * X) * Den178 X
        * (B178 (p * X) * (U p (6 * (p * X)) * U p (5 * (p * X)) * U p (p * X) * L178 p X))
      = B178 (p * X) * (p ^ (13 * X) * Den178 X
          * (U p (6 * (p * X)) * U p (5 * (p * X)) * U p (p * X) * L178 p X)) := by ring
    _ = B178 (p * X) * Den178 (p * X) := by rw [hDenY]
    _ = Num178 (p * X) := B178_mul_den (p * X)
    _ = 2 ^ (p * X - X) * p ^ (13 * X) * (U p (10 * (p * X)) * U p (3 * (p * X))) * Num178 X :=
        hNumY
    _ = 2 ^ (p * X - X) * p ^ (13 * X) * (U p (10 * (p * X)) * U p (3 * (p * X)))
          * (B178 X * Den178 X) := by rw [B178_mul_den X]
    _ = p ^ (13 * X) * Den178 X
          * (2 ^ (p * X - X) * (U p (10 * (p * X)) * U p (3 * (p * X))) * B178 X) := by ring

/-! ### The tower in `ZMod (p^(3r))` -/

theorem B178_congr (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    B178 (n * p ^ r) ≡ B178 (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
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
  have key := key_identity p X hp.pos
  have hcast := congrArg (fun k : ℕ => (k : ZMod (p ^ (3 * r)))) key
  push_cast at hcast
  -- the unit products
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
  have h2unit : IsUnit (2 : ZMod (p ^ (3 * r))) := by
    have hcop : Nat.Coprime 2 (p ^ (3 * r)) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have := (ZMod.isUnit_iff_coprime 2 (p ^ (3 * r))).mpr hcop
    simpa using this
  have hL : ((L178 p X : ℕ) : ZMod (p ^ (3 * r))) = 2 ^ (p * X - X) * W ^ n := by
    unfold L178
    push_cast
    have h := prod_units_linear p r n hp hp5 hr 2 (n : ZMod (p ^ (3 * r))) h2unit
    rw [show n * p ^ r = p * X by rw [hX, hpr]; ring] at h
    have hpX : (p : ZMod (p ^ (3 * r))) * (X : ZMod (p ^ (3 * r)))
        = (n : ZMod (p ^ (3 * r))) * (p : ZMod (p ^ (3 * r))) ^ r := by
      have h' : ((p * X : ℕ) : ZMod (p ^ (3 * r))) = ((n * p ^ r : ℕ) : ZMod (p ^ (3 * r))) := by
        rw [hY]
      push_cast at h'
      exact h'
    have e : ∀ j ∈ (range (p * X)).filter (fun j => ¬ p ∣ j),
        ((p : ZMod (p ^ (3 * r))) * (X : ZMod (p ^ (3 * r))) + 2 * (j : ZMod (p ^ (3 * r))))
          = 2 * (j : ZMod (p ^ (3 * r)))
            + (n : ZMod (p ^ (3 * r))) * (p : ZMod (p ^ (3 * r))) ^ r := by
      intro j _
      linear_combination hpX
    rw [prod_congr rfl e, h, prod_mul_distrib, prod_const, card_filter_not_dvd_range_mul p X hp.pos]
    congr 1
    have h1 := hU1
    unfold U at h1
    push_cast at h1
    exact h1
  rw [hU 6, hU 5, hU1, hU 10, hU 3, hL] at hcast
  have hunit : IsUnit ((2 : ZMod (p ^ (3 * r))) ^ (p * X - X) * W ^ (13 * n)) :=
    (h2unit.pow _).mul ((isUnit_W p r hp).pow _)
  apply hunit.mul_right_cancel
  calc (B178 (p * X) : ZMod (p ^ (3 * r))) * (2 ^ (p * X - X) * W ^ (13 * n))
      = (B178 (p * X) : ZMod (p ^ (3 * r)))
          * (W ^ (6 * n) * W ^ (5 * n) * W ^ n * (2 ^ (p * X - X) * W ^ n)) := by ring
    _ = 2 ^ (p * X - X) * (W ^ (10 * n) * W ^ (3 * n)) * (B178 X : ZMod (p ^ (3 * r))) := hcast
    _ = (B178 X : ZMod (p ^ (3 * r))) * (2 ^ (p * X - X) * W ^ (13 * n)) := by ring

end Bala

/-! ### The benchmark statement (`lean-targets/364178_4c681d65.lean`) -/

open Real

/--
A364178: The conjecturally integral sequence
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$
where $x! := \Gamma(x+1)$ for real $x$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat

namespace Bala

/-- the Γ-quotient of the benchmark equals the integer form -/
theorem val_eq (n : ℕ) :
    (Real.Gamma (10 * (n : ℝ) + 1) * Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma ((n : ℝ) / 2 + 1)) /
      (Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (5 * (n : ℝ) + 1) * Real.Gamma (3 * (n : ℝ) / 2 + 1)
        * Real.Gamma ((n : ℝ) + 1))
      = (Num178 n : ℝ) / (Den178 n : ℝ) := by
  have h10 : Real.Gamma (10 * (n : ℝ) + 1) = ((10 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (10 * n)
    push_cast at h
    exact h
  have h3 : Real.Gamma (3 * (n : ℝ) + 1) = ((3 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (3 * n)
    push_cast at h
    exact h
  have h6 : Real.Gamma (6 * (n : ℝ) + 1) = ((6 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (6 * n)
    push_cast at h
    exact h
  have h5 : Real.Gamma (5 * (n : ℝ) + 1) = ((5 * n).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (5 * n)
    push_cast at h
    exact h
  have h1 : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
  have hx : (0 : ℝ) < (n : ℝ) / 2 + 1 := by positivity
  have hhalf : Real.Gamma (3 * (n : ℝ) / 2 + 1)
      = Real.Gamma ((n : ℝ) / 2 + 1) * ∏ j ∈ range n, ((n : ℝ) / 2 + 1 + j) := by
    rw [← Gamma_add_nat_eq _ hx n]
    congr 1
    ring
  have hP : ∏ j ∈ range n, ((n : ℝ) / 2 + 1 + j)
      = ((∏ j ∈ Icc 1 n, (n + 2 * j) : ℕ) : ℝ) / 2 ^ n := by
    push_cast
    rw [prod_Icc_one_eq_prod_range]
    have h2 : (2 : ℝ) ^ n = ∏ _j ∈ range n, (2 : ℝ) := by
      rw [prod_const, card_range]
    rw [h2, ← prod_div_distrib]
    apply prod_congr rfl
    intro j _
    push_cast
    ring
  rw [h10, h3, h6, h5, h1, hhalf, hP]
  unfold Num178 Den178
  push_cast
  have hG : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hPne : (∏ j ∈ Icc 1 n, ((n : ℝ) + 2 * (j : ℝ))) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro j hj
    simp only [mem_Icc] at hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    positivity
  have hf10 : ((10 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf3 : ((3 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf6 : ((6 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf5 : ((5 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf1 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- the benchmark's `a n` is the integer `Num178 n / Den178 n` -/
theorem a_eq_B178 (n : ℕ) : a n = B178 n := by
  have hdvd := den_dvd_num n
  have hden : (Den178 n : ℝ) ≠ 0 := by exact_mod_cast (Den178_pos n).ne'
  unfold a B178
  rw [val_eq n, ← Nat.cast_div hdvd hden, round_natCast, Int.toNat_natCast]

end Bala

open Bala in
/-- A364178 Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r. -/
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  rw [a_eq_B178, a_eq_B178]
  exact B178_congr p n r hp h5 hr
