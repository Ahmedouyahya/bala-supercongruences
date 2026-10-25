import BalaProofs.A386548Defs

/-!
# A386548, step 1: the identity `a N = S N` for `N ≥ 1`

`a` is the sequence of the Formal Conjectures file `FormalConjectures/OEIS/Auto/386548_8788c4f8.lean`
(imported, not copied).  `S N = Σ_{2j+3m=N} (-1)^(j+m) C(N,j) C(N+m-1,m)` is the expansion of
`(1-x²)^N (1+x³)^(-N)`, while `a N` is the expansion of `(1 + x²/(1-x))^(-N)`; the two series agree
because `(1 + x²/(1-x)) (1 - x²) = 1 + x³`.  Both are obtained by substituting into
`Bser d = (1+X)^(-(d+1))` (`N = d+1`) with `PowerSeries.subst`.
-/

open Finset PowerSeries

namespace A386548

/-- Summand of `S N` indexed by `j`, with `m = (N - 2j)/3` (zero unless `2j + 3m = N`). -/
def t (N j : ℕ) : ℤ :=
  if 2 * j ≤ N ∧ 3 ∣ (N - 2 * j) then
    (-1 : ℤ) ^ (j + (N - 2 * j) / 3) * ((N.choose j : ℕ) : ℤ)
      * (((N + (N - 2 * j) / 3 - 1).choose ((N - 2 * j) / 3) : ℕ) : ℤ)
  else 0

/-- `S N = Σ_{2j+3m=N} (-1)^(j+m) C(N,j) C(N+m-1,m)`. -/
def S (N : ℕ) : ℤ := ∑ j ∈ range (N + 1), t N j

/-- `Bser d = (1 + X)^(-(d+1))`. -/
noncomputable def Bser (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ) ^ n * ((Nat.choose (d + n) d : ℕ) : ℤ)

lemma Bser_mul (d : ℕ) : Bser d * (1 + X) ^ (d + 1) = 1 := by
  have h := mk_add_choose_mul_one_sub_pow_eq_one (S := ℤ) (d := d)
  have h2 := congrArg (rescale (-1 : ℤ)) h
  rw [map_mul, map_pow, map_sub, map_one, rescale_neg_one_X, sub_neg_eq_add] at h2
  convert h2 using 2
  ext n
  simp [Bser, coeff_rescale, coeff_mk]

/-- `U = X² / (1 - X)`. -/
noncomputable def U : PowerSeries ℤ := X ^ 2 * PowerSeries.mk 1

lemma hasSubst_U : HasSubst U :=
  HasSubst.of_constantCoeff_zero' (by simp [U])

lemma hasSubst_X3 : HasSubst (X ^ 3 : PowerSeries ℤ) :=
  HasSubst.of_constantCoeff_zero' (by simp)

lemma subst_Bser_mul {b : PowerSeries ℤ} (hb : HasSubst b) (d : ℕ) :
    (Bser d).subst b * (1 + b) ^ (d + 1) = 1 := by
  have h := congrArg (substAlgHom (R := ℤ) hb) (Bser_mul d)
  simp only [map_mul, map_pow, map_add, map_one, substAlgHom_X] at h
  rw [← coe_substAlgHom hb]
  exact h

lemma U_key : (1 + U) * (1 - X ^ 2) = 1 + X ^ 3 := by
  have h := mk_one_mul_one_sub_eq_one ℤ
  unfold U
  linear_combination (X ^ 2 * (1 + X)) * h

lemma series_eq (d : ℕ) :
    (Bser d).subst U = (1 - X ^ 2) ^ (d + 1) * (Bser d).subst (X ^ 3 : PowerSeries ℤ) := by
  have hA := subst_Bser_mul hasSubst_U d
  have hW := subst_Bser_mul hasSubst_X3 d
  have hk : ((1 + U) * (1 - X ^ 2)) ^ (d + 1) = (1 + X ^ 3 : PowerSeries ℤ) ^ (d + 1) := by
    rw [U_key]
  rw [mul_pow] at hk
  linear_combination ((1 - X ^ 2) ^ (d + 1) * (Bser d).subst (X ^ 3 : PowerSeries ℤ)) * hA
    - ((Bser d).subst U) * hW
    - ((Bser d).subst U * (Bser d).subst (X ^ 3 : PowerSeries ℤ)) * hk

lemma coeff_U_pow (N k : ℕ) :
    coeff N (U ^ k) =
      if 2 * k ≤ N then coeff (N - 2 * k) ((PowerSeries.mk 1 : PowerSeries ℤ) ^ k) else 0 := by
  rw [U, mul_pow, ← pow_mul, coeff_X_pow_mul']

lemma sign_eq (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rw [neg_one_pow_eq_ite]
  simp [Nat.even_iff]

lemma coeff_subst_U (d : ℕ) : coeff (d + 1) ((Bser d).subst U) = a (d + 1) := by
  have hsupp : Function.support (fun k => coeff k (Bser d) • coeff (d + 1) (U ^ k))
      ⊆ ↑(range ((d + 1) / 2 + 1)) := by
    intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [coeff_U_pow, if_neg (by omega), smul_zero]
  rw [coeff_subst' hasSubst_U, finsum_eq_sum_of_support_subset _ hsupp]
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 * k ≤ d + 1 := by rw [mem_range] at hk; omega
  simp only [Bser, coeff_mk, smul_eq_mul, coeff_U_pow, if_pos hk2]
  rw [← sign_eq, show d + 1 + k - 1 = d + k by omega]
  have c1 : Nat.choose (d + k) d = Nat.choose (d + k) k := Nat.choose_symm_add
  rw [c1]
  rcases k with _ | k
  · simp [coeff_one]
  · rw [mk_one_pow_eq_mk_choose_add, coeff_mk]
    have e : d + 1 - (k + 1) - 1 = k + (d + 1 - 2 * (k + 1)) := by omega
    have c2 : Nat.choose (k + (d + 1 - 2 * (k + 1))) k
        = Nat.choose (k + (d + 1 - 2 * (k + 1))) (d + 1 - 2 * (k + 1)) := Nat.choose_symm_add
    rw [e, c2]

lemma coeff_subst_X3 (d m : ℕ) :
    coeff m ((Bser d).subst (X ^ 3 : PowerSeries ℤ)) =
      if 3 ∣ m then (-1 : ℤ) ^ (m / 3) * ((Nat.choose (d + m / 3) d : ℕ) : ℤ) else 0 := by
  rw [coeff_subst' hasSubst_X3]
  simp only [← pow_mul, coeff_X_pow]
  split_ifs with h3
  · obtain ⟨c, rfl⟩ := h3
    rw [finsum_eq_single _ c]
    · simp [Bser, coeff_mk]
    · intro e he
      rw [if_neg (by omega), smul_zero]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro e
    rw [if_neg (fun h => h3 ⟨e, h⟩), smul_zero]

lemma one_sub_X2_pow (N : ℕ) :
    (1 - X ^ 2 : PowerSeries ℤ) ^ N =
      ∑ j ∈ range (N + 1), C ((-1 : ℤ) ^ j * ((N.choose j : ℕ) : ℤ)) * X ^ (2 * j) := by
  rw [show (1 - X ^ 2 : PowerSeries ℤ) = C (-1) * X ^ 2 + 1 by rw [map_neg, map_one]; ring, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow, mul_one, mul_pow, ← map_pow, ← pow_mul, map_mul, map_natCast]
  ring

lemma coeff_rhs (d : ℕ) :
    coeff (d + 1) ((1 - X ^ 2) ^ (d + 1) * (Bser d).subst (X ^ 3 : PowerSeries ℤ)) = S (d + 1) := by
  rw [one_sub_X2_pow, Finset.sum_mul, map_sum]
  unfold S
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_subst_X3]
  unfold t
  by_cases h1 : 2 * j ≤ d + 1
  · by_cases h2 : 3 ∣ (d + 1 - 2 * j)
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      have c1 : d + 1 + (d + 1 - 2 * j) / 3 - 1 = d + (d + 1 - 2 * j) / 3 := by omega
      have c2 : Nat.choose (d + (d + 1 - 2 * j) / 3) d
          = Nat.choose (d + (d + 1 - 2 * j) / 3) ((d + 1 - 2 * j) / 3) := Nat.choose_symm_add
      rw [c1, c2, pow_add]
      ring
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
      ring
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    ring

/-- **Step 1.** For `N ≥ 1`, `a N = S N`. -/
theorem a_eq_S (N : ℕ) (hN : 1 ≤ N) : a N = S N := by
  obtain ⟨d, rfl⟩ : ∃ d, N = d + 1 := ⟨N - 1, by omega⟩
  rw [← coeff_subst_U, series_eq, coeff_rhs]

end A386548
