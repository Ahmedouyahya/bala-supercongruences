import BalaCheck.EpochJac

/-!
# A386548, step 4: the scaled terms

For `2j + 3m = M`, `p ≥ 5` prime:
`p^(2 v_p(M) + 3) ∣ C(pM,pj) C(p(M+m)-1,pm) - C(M,j) C(M+m-1,m)`,
from the strong Kazandzidis congruence `Epoch361883.JAC_bound` (Epoch AI's accepted Lean proof,
`BalaCheck/EpochJac.lean`, imported unchanged).
-/

open Nat

namespace A386548

variable (p : ℕ) [Fact p.Prime]

/-- Bridge `ℤ` ↔ `ℤ_[p]` for divisibility by `p^s`. -/
lemma int_dvd_iff_padic_dvd (s : ℕ) (z : ℤ) :
    (p : ℤ) ^ s ∣ z ↔ (p : ℤ_[p]) ^ s ∣ (z : ℤ_[p]) := by
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩
  rw [← Epoch361883.toZModPow_eq_zero_iff_dvd, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- `p^(v_p n) ∣ n` in `ℤ_[p]`. -/
lemma padic_pow_fact_dvd (n : ℕ) : (p : ℤ_[p]) ^ (n.factorization p) ∣ (n : ℤ_[p]) :=
  (Epoch361883.nat_dvd_iff_padic_dvd p _ n).mp (Nat.ordProj_dvd n p)

/-- Cancelling a natural factor `D ≠ 0` costs exactly `v_p D`. -/
lemma padic_cancel (D : ℕ) (hD : D ≠ 0) (e : ℕ) (x : ℤ_[p])
    (h : (p : ℤ_[p]) ^ (e + D.factorization p) ∣ (D : ℤ_[p]) * x) : (p : ℤ_[p]) ^ e ∣ x := by
  have hp : p.Prime := Fact.out
  have hDe : (D : ℤ_[p]) = (p : ℤ_[p]) ^ (D.factorization p)
      * ((D / p ^ D.factorization p : ℕ) : ℤ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hu : IsUnit ((D / p ^ D.factorization p : ℕ) : ℤ_[p]) :=
    Epoch361883.isUnit_nat_of_not_dvd p (Nat.not_dvd_ordCompl hp hD)
  rw [hDe, mul_assoc, pow_add, mul_comm ((p : ℤ_[p]) ^ e)] at h
  have hp0 : (p : ℤ_[p]) ^ (D.factorization p) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have h2 := (mul_dvd_mul_iff_left hp0).mp h
  exact hu.dvd_mul_left.mp h2

/-- `v_p M ≤ v_p j + v_p C(M,j)` for `1 ≤ j ≤ M` (from `j C(M,j) = M C(M-1,j-1)`). -/
lemma fact_le_choose (M j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M) :
    M.factorization p ≤ j.factorization p + (M.choose j).factorization p := by
  have hp : p.Prime := Fact.out
  have hj0 : j ≠ 0 := by omega
  have hC0 : M.choose j ≠ 0 := (Nat.choose_pos hjM).ne'
  have hdvd : M ∣ j * M.choose j :=
    ⟨(M - 1).choose (j - 1), Epoch361883.choose_absorb_low M j hj1 hjM⟩
  have hpw : p ^ M.factorization p ∣ j * M.choose j := (Nat.ordProj_dvd M p).trans hdvd
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (mul_ne_zero hj0 hC0)).mp hpw
  rwa [Nat.factorization_mul hj0 hC0, Finsupp.add_apply] at hle

/-- First factor: `p^(2 v_p M + 3) ∣ C(pM,pj) - C(M,j)` for `2j ≤ M`. -/
lemma factor1 (hp5 : 5 ≤ p) (M j : ℕ) (hj : 2 * j ≤ M) :
    (p : ℤ_[p]) ^ (2 * M.factorization p + 3) ∣
      (((p * M).choose (p * j) : ℕ) : ℤ_[p]) - ((M.choose j : ℕ) : ℤ_[p]) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · simp
  have hJ := Epoch361883.JAC_bound p (M - j) j hp5 hj1 (by omega)
  have e : M - j + j = M := by omega
  rw [e] at hJ
  refine dvd_trans (pow_dvd_pow _ ?_) hJ
  have := fact_le_choose p M j hj1 (by omega)
  omega

/-- Second factor: `p^(2 v_p M + 3) ∣ C(p(M+m)-1,pm) - C(M+m-1,m)` for `m ≤ M`. -/
lemma factor2 (hp5 : 5 ≤ p) (M m : ℕ) (hm : m ≤ M) :
    (p : ℤ_[p]) ^ (2 * M.factorization p + 3) ∣
      (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ_[p]) - (((M + m - 1).choose m : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp
  have hJ := Epoch361883.JAC_bound p M m hp5 hm1 hm
  have hA := Epoch361883.stepA_At p (M + m) m hp.one_lt.le hm1 (by omega)
  have hB := Epoch361883.stepA_Bt (M + m) m hm1 (by omega)
  rw [Nat.add_sub_cancel] at hA hB
  have key : ((M + m : ℕ) : ℤ_[p]) * ((((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ_[p])
        - (((M + m - 1).choose m : ℕ) : ℤ_[p]))
      = (M : ℤ_[p]) * ((((p * (M + m)).choose (p * m) : ℕ) : ℤ_[p])
        - (((M + m).choose m : ℕ) : ℤ_[p])) := by
    have hA' := congrArg (Nat.cast : ℕ → ℤ_[p]) hA
    have hB' := congrArg (Nat.cast : ℕ → ℤ_[p]) hB
    simp only [Nat.cast_mul] at hA' hB'
    rw [mul_sub, mul_sub, hA', hB']
  apply padic_cancel p (M + m) (by omega)
  rw [key]
  have hprod := mul_dvd_mul (padic_pow_fact_dvd p M) hJ
  rw [← pow_add] at hprod
  refine dvd_trans (pow_dvd_pow _ ?_) hprod
  omega

/-- **Step 4 (scaled terms), in `ℤ`.** -/
lemma scaled_int (hp5 : 5 ≤ p) (M j m : ℕ) (h : 2 * j + 3 * m = M) :
    (p : ℤ) ^ (2 * M.factorization p + 3) ∣
      (((p * M).choose (p * j) : ℕ) : ℤ) * (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ)
        - ((M.choose j : ℕ) : ℤ) * (((M + m - 1).choose m : ℕ) : ℤ) := by
  rw [int_dvd_iff_padic_dvd]
  have h1 := factor1 p hp5 M j (by omega)
  have h2 := factor2 p hp5 M m (by omega)
  push_cast
  have e : (((p * M).choose (p * j) : ℕ) : ℤ_[p]) * (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ_[p])
        - ((M.choose j : ℕ) : ℤ_[p]) * (((M + m - 1).choose m : ℕ) : ℤ_[p])
      = ((((p * M).choose (p * j) : ℕ) : ℤ_[p]) - ((M.choose j : ℕ) : ℤ_[p]))
          * (((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ_[p])
        + ((M.choose j : ℕ) : ℤ_[p]) * ((((p * (M + m) - 1).choose (p * m) : ℕ) : ℤ_[p])
          - (((M + m - 1).choose m : ℕ) : ℤ_[p])) := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

end A386548
