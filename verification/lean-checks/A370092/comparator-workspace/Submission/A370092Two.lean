import Submission.A370092Formula

/-!
# A370092, Part 3: powers of two (elementary replacement of Amice's theorem)

With `P = 2^(m+1)`, `n ≥ m + 3` and `F j = j^n (j^P - 1)`:
Lemma B: `2^(m + 2 + ⌊k/3⌋) ∣ fdiff k F`; hence `2^(m+2) ∣ A (n + 2^(m+1)) - A n`.
(PLAN.md's `m` is `m + 1` here.)
-/

open Finset Polynomial

namespace A370092

/-- `F n P j = j^n (j^P - 1)`. -/
def F (n P : ℕ) (j : ℕ) : ℤ := (j : ℤ) ^ n * ((j : ℤ) ^ P - 1)

/- ### (i) The operator identity via `ℤ[X]` -/

/-- The linear functional `X^s ↦ f s`. -/
noncomputable def L (f : ℕ → ℤ) : ℤ[X] →ₗ[ℤ] ℤ :=
  Polynomial.lsum (fun s => LinearMap.smulRight LinearMap.id (f s))

theorem L_monomial (f : ℕ → ℤ) (s : ℕ) (c : ℤ) : L f (monomial s c) = c * f s := by
  simp [L, Polynomial.lsum_apply, sum_monomial_index]

theorem L_C_mul (f : ℕ → ℤ) (c : ℤ) (p : ℤ[X]) : L f (C c * p) = c * L f p := by
  rw [C_mul', map_smul, smul_eq_mul]

theorem X_sub_one_pow_eq (k : ℕ) : (X - 1 : ℤ[X]) ^ k =
    ∑ m ∈ range (k + 1), C ((-1 : ℤ) ^ (m + k) * (k.choose m : ℤ)) * X ^ m := by
  rw [sub_pow]
  refine sum_congr rfl fun m _ => ?_
  simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem L_X_sub_one_pow (f : ℕ → ℤ) (k : ℕ) : L f ((X - 1) ^ k) = fdiff k f := by
  rw [X_sub_one_pow_eq, map_sum]
  unfold fdiff
  refine sum_congr rfl fun m _ => ?_
  rw [C_mul_X_pow_eq_monomial, L_monomial]

theorem L_X_pow_mul_expand (f : ℕ → ℤ) (l : ℕ) (p : ℤ[X]) :
    L f (X ^ l * expand ℤ 2 p) = L (fun t => f (l + 2 * t)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, map_add, map_add, hp, hq]
  | monomial t c =>
    rw [expand_monomial, X_pow_mul_monomial, L_monomial, L_monomial,
      show t * 2 + l = l + 2 * t by ring]

theorem L_X_sub_one_pow_mul_expand (f : ℕ → ℤ) (r : ℕ) (p : ℤ[X]) :
    L f ((X - 1) ^ r * expand ℤ 2 p) = ∑ l ∈ range (r + 1),
      (-1 : ℤ) ^ (l + r) * (r.choose l : ℤ) * L (fun t => f (l + 2 * t)) p := by
  rw [X_sub_one_pow_eq, sum_mul, map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_assoc, L_C_mul, L_X_pow_mul_expand]

theorem poly_identity (r e : ℕ) : ((X - 1 : ℤ[X]) ^ (2 * r + e)) = ∑ i ∈ range (r + 1),
    ((r.choose i : ℤ) * (-2) ^ i) • ((X - 1) ^ (i + e) * expand ℤ 2 ((X - 1) ^ (r - i))) := by
  have hsq : (X - 1 : ℤ[X]) ^ 2 = (-2 : ℤ[X]) * (X - 1) + expand ℤ 2 (X - 1) := by
    simp only [map_sub, expand_X, map_one]; ring
  rw [show 2 * r + e = e + 2 * r by ring, pow_add, pow_mul, hsq, add_pow, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, map_pow, mul_pow]
  push_cast
  ring

theorem op_identity (f : ℕ → ℤ) (r e : ℕ) :
    fdiff (2 * r + e) f = ∑ i ∈ range (r + 1), ((r.choose i : ℤ) * (-2) ^ i) *
      ∑ l ∈ range (i + e + 1), (-1 : ℤ) ^ (l + (i + e)) * ((i + e).choose l : ℤ) *
        fdiff (r - i) (fun t => f (l + 2 * t)) := by
  rw [← L_X_sub_one_pow, poly_identity, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, L_X_sub_one_pow_mul_expand]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [L_X_sub_one_pow]

/- ### (ii) Differences of polynomial functions -/

theorem factorial_dvd_fdiff_eval (b : ℕ) (Q : ℤ[X]) :
    (b.factorial : ℤ) ∣ fdiff b (fun t => Q.eval (t : ℤ)) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    rw [fdiff_add]; exact dvd_add hp hq
  | monomial s c =>
    simp only [eval_monomial]
    rw [fdiff_const_mul]
    apply dvd_mul_of_dvd_right
    have := factorial_dvd_D s 0 b
    unfold D at this; simpa using this

theorem fdiff_dvd_of_poly (b s : ℕ) (φ : ℕ → ℤ) (Q : ℤ[X])
    (hQ : ∀ t : ℕ, φ t = 2 ^ s * Q.eval (t : ℤ)) : (2 ^ s * b.factorial : ℤ) ∣ fdiff b φ := by
  have : φ = fun t : ℕ => 2 ^ s * Q.eval (t : ℤ) := funext hQ
  rw [this, fdiff_const_mul]
  exact mul_dvd_mul_left _ (factorial_dvd_fdiff_eval b Q)

/- ### (iii) `(1+2y)^(2^(m+1)) = 1 + 2^(m+2) y(y+1) + 2^(m+3) R(y)` -/

theorem one_add_two_pow (m : ℕ) : ∃ R : ℤ[X], ∀ y : ℤ,
    (1 + 2 * y) ^ (2 ^ (m + 1)) = 1 + 2 ^ (m + 2) * (y * (y + 1)) + 2 ^ (m + 3) * R.eval y := by
  induction m with
  | zero => exact ⟨0, fun y => by simp only [eval_zero, mul_zero, add_zero]; ring⟩
  | succ m ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + C (2 ^ m) * (X * (X + 1) + 2 * R) ^ 2, fun y => ?_⟩
    rw [pow_succ 2 (m + 1), pow_mul, hR y]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_ofNat]
    ring

/- ### (iv) The two residue classes -/

theorem F_even (n P l : ℕ) :
    ∃ Q : ℤ[X], ∀ t : ℕ, F n P (2 * l + 2 * t) = 2 ^ n * Q.eval (t : ℤ) := by
  refine ⟨(X + C (l : ℤ)) ^ n * ((C 2 * (X + C (l : ℤ))) ^ P - 1), fun t => ?_⟩
  simp only [F, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_sub, eval_one]
  push_cast
  rw [show (2 * (l : ℤ) + 2 * t) = 2 * ((t : ℤ) + l) by ring, mul_pow]
  ring

theorem F_odd (n m l : ℕ) :
    ∃ Q : ℤ[X], ∀ t : ℕ, F n (2 ^ (m + 1)) (2 * l + 1 + 2 * t) = 2 ^ (m + 2) * Q.eval (t : ℤ) := by
  obtain ⟨R, hR⟩ := one_add_two_pow m
  refine ⟨(1 + 2 * (X + C (l : ℤ))) ^ n * ((X + C (l : ℤ)) * (X + C (l : ℤ) + 1) +
    2 * R.comp (X + C (l : ℤ))), fun t => ?_⟩
  simp only [F]
  push_cast
  rw [show (2 * (l : ℤ) + 1 + 2 * t) = 1 + 2 * ((t : ℤ) + l) by ring, hR]
  simp only [eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_one, eval_comp, eval_ofNat]
  ring

theorem F_one (n m : ℕ) : ∃ Q : ℤ[X], ∀ t : ℕ, F n (2 ^ (m + 1)) (1 + 2 * t) =
    2 ^ (m + 2) * ((t : ℤ) * (t + 1)) + 2 ^ (m + 3) * Q.eval (t : ℤ) := by
  obtain ⟨R, hR⟩ := one_add_two_pow m
  obtain ⟨W, hW⟩ := sub_dvd_pow_sub_pow (1 + 2 * X : ℤ[X]) 1 n
  have hW' : ∀ y : ℤ, (1 + 2 * y) ^ n = 1 + 2 * y * W.eval y := by
    intro y
    have := congrArg (eval y) hW
    simp only [eval_sub, eval_pow, eval_add, eval_mul, eval_X, eval_one, one_pow,
      eval_ofNat] at this
    linear_combination this
  refine ⟨R + X * W * (X * (X + 1)) + 2 * X * W * R, fun t => ?_⟩
  simp only [F]
  push_cast
  rw [hR, hW']
  simp only [eval_mul, eval_add, eval_X, eval_one, eval_ofNat]
  ring

theorem class_bound_even (n P l b : ℕ) :
    (2 ^ n * b.factorial : ℤ) ∣ fdiff b (fun t => F n P (2 * l + 2 * t)) := by
  obtain ⟨Q, hQ⟩ := F_even n P l
  exact fdiff_dvd_of_poly b n _ Q hQ

theorem class_bound (n m l b : ℕ) (hn : m + 3 ≤ n) :
    (2 ^ (m + 2) * b.factorial : ℤ) ∣ fdiff b (fun t => F n (2 ^ (m + 1)) (l + 2 * t)) := by
  rcases Nat.even_or_odd' l with ⟨l', rfl | rfl⟩
  · exact (mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) _).trans (class_bound_even n _ l' b)
  · obtain ⟨Q, hQ⟩ := F_odd n m l'
    exact fdiff_dvd_of_poly b (m + 2) _ Q hQ

theorem fdiff_tt1 (r : ℕ) (hr : r ≠ 2) :
    (2 * r.factorial : ℤ) ∣ fdiff r (fun t => (t : ℤ) * (t + 1)) := by
  match r, hr with
  | 0, _ => simp [fdiff]
  | 1, _ => norm_num [fdiff, sum_range_succ]
  | 2, h => exact absurd rfl h
  | (r + 3), _ =>
    have : fdiff (r + 3) (fun t => (t : ℤ) * (t + 1)) = D 0 (r + 3) 2 + D 0 (r + 3) 1 := by
      unfold D; rw [← fdiff_add]; congr 1; funext t; ring
    rw [this, D_eq_zero 2 0 (r + 3) (by omega), D_eq_zero 1 0 (r + 3) (by omega)]; simp

theorem class_bound_one (n m r : ℕ) (hr : r ≠ 2) :
    (2 ^ (m + 3) * r.factorial : ℤ) ∣ fdiff r (fun t => F n (2 ^ (m + 1)) (1 + 2 * t)) := by
  obtain ⟨Q, hQ⟩ := F_one n m
  have : (fun t => F n (2 ^ (m + 1)) (1 + 2 * t)) =
      fun t : ℕ => 2 ^ (m + 2) * ((t : ℤ) * (t + 1)) + 2 ^ (m + 3) * Q.eval (t : ℤ) := funext hQ
  rw [this, fdiff_add, fdiff_const_mul, fdiff_const_mul]
  apply dvd_add
  · obtain ⟨c, hc⟩ := fdiff_tt1 r hr
    rw [hc]; exact ⟨c, by ring⟩
  · exact mul_dvd_mul_left _ (factorial_dvd_fdiff_eval r Q)

/- ### (v)–(vii) 2-adic bookkeeping and Lemma B -/

theorem not_two_pow_dvd_factorial (i : ℕ) (hi : 1 ≤ i) : ¬ 2 ^ i ∣ i.factorial := by
  intro h
  have h1 := Nat.emultiplicity_two_factorial_lt (show i ≠ 0 by omega)
  have h2 := (pow_dvd_iff_le_emultiplicity).mp h
  exact absurd h2 (not_le.mpr h1)

theorem two_pow_aux (Y i s : ℕ) (hi : 1 ≤ i) (hY : Y ≠ 0) (h : 2 ^ s ∣ Y * i.factorial) :
    2 ^ (s + 1) ∣ Y * 2 ^ i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : i.factorial ≠ 0 := Nat.factorial_ne_zero i
  have hv : padicValNat 2 i.factorial < i := by
    by_contra hc; push_neg at hc
    exact not_two_pow_dvd_factorial i hi ((padicValNat_dvd_iff_le hf).mpr hc)
  have h1 := (padicValNat_dvd_iff_le (mul_ne_zero hY hf)).mp h
  rw [padicValNat.mul hY hf] at h1
  rw [padicValNat_dvd_iff_le (mul_ne_zero hY (by positivity)), padicValNat.mul hY (by positivity),
    padicValNat.prime_pow]
  omega

theorem two_pow_fact4 (r : ℕ) : 2 ^ (r / 2 + r / 4) ∣ r.factorial := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | (r + 4), ih =>
      have ih0 := ih r (by omega)
      rw [show (r + 4) / 2 + (r + 4) / 4 = (r / 2 + r / 4) + 3 by omega, pow_add]
      have h24 : r.factorial * (4).factorial ∣ (r + 4).factorial :=
        Nat.factorial_mul_factorial_dvd_factorial_add r 4
      have h8 : 2 ^ 3 ∣ (4).factorial := by decide
      exact (mul_dvd_mul ih0 h8).trans h24

/-- The `i`-th term of the operator identity for `F`. -/
def T (n m r e i : ℕ) : ℤ := ((r.choose i : ℤ) * (-2) ^ i) *
  ∑ l ∈ range (i + e + 1), (-1 : ℤ) ^ (l + (i + e)) * ((i + e).choose l : ℤ) *
    fdiff (r - i) (fun t => F n (2 ^ (m + 1)) (l + 2 * t))

theorem T_bound (n m r e i s : ℕ) (hn : m + 3 ≤ n) (hi : 1 ≤ i) (hir : i ≤ r)
    (hs : 2 ^ s ∣ r.factorial) : (2 : ℤ) ^ (m + 3 + s) ∣ T n m r e i := by
  unfold T
  have hS : (2 ^ (m + 2) * (r - i).factorial : ℤ) ∣ ∑ l ∈ range (i + e + 1),
      (-1 : ℤ) ^ (l + (i + e)) * ((i + e).choose l : ℤ) *
        fdiff (r - i) (fun t => F n (2 ^ (m + 1)) (l + 2 * t)) :=
    dvd_sum fun l _ => dvd_mul_of_dvd_right (class_bound n m l (r - i) hn) _
  have h2i : (2 : ℤ) ^ i ∣ (-2) ^ i := pow_dvd_pow_of_dvd (by norm_num) i
  have hY : 2 ^ (s + 1) ∣ (r.choose i * (r - i).factorial) * 2 ^ i := by
    apply two_pow_aux _ i s hi (mul_ne_zero (Nat.choose_pos hir).ne' (Nat.factorial_ne_zero _))
    rw [mul_right_comm, Nat.choose_mul_factorial_mul_factorial hir]
    exact hs
  have hY' : (2 : ℤ) ^ (s + 1) ∣ (r.choose i : ℤ) * ((r - i).factorial : ℤ) * 2 ^ i := by
    exact_mod_cast hY
  refine dvd_trans ?_ (mul_dvd_mul (mul_dvd_mul_left _ h2i) hS)
  have : (2 : ℤ) ^ (m + 3 + s) = 2 ^ (m + 2) * 2 ^ (s + 1) := by rw [← pow_add]; ring_nf
  rw [this]
  obtain ⟨c, hc⟩ := hY'
  exact ⟨c, by linear_combination (2 : ℤ) ^ (m + 2) * hc⟩

theorem T_zero_bound (n m r e : ℕ) (hn : m + 3 ≤ n) :
    (2 ^ (m + 2) * r.factorial : ℤ) ∣ T n m r e 0 := by
  unfold T
  simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul, Nat.sub_zero, zero_add]
  exact dvd_sum fun l _ => dvd_mul_of_dvd_right (class_bound n m l r hn) _

theorem T_zero_bound' (n m r e : ℕ) (hn : m + 3 ≤ n) (he : e < 2) (hr : r ≠ 2) :
    (2 ^ (m + 3) * r.factorial : ℤ) ∣ T n m r e 0 := by
  have heven : (2 ^ (m + 3) * r.factorial : ℤ) ∣ fdiff r (fun t => F n (2 ^ (m + 1)) (0 + 2 * t)) := by
    have := class_bound_even n (2 ^ (m + 1)) 0 r
    simp only [mul_zero, zero_add] at this ⊢
    exact (mul_dvd_mul_right (pow_dvd_pow 2 hn) _).trans this
  unfold T
  simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul, Nat.sub_zero, zero_add]
  interval_cases e
  · rw [sum_range_one]
    exact dvd_mul_of_dvd_right (by simpa using heven) _
  · rw [sum_range_succ, sum_range_one]
    apply dvd_add
    · exact dvd_mul_of_dvd_right (by simpa using heven) _
    · exact dvd_mul_of_dvd_right (class_bound_one n m r hr) _

theorem lemmaB (n m k : ℕ) (hn : m + 3 ≤ n) :
    (2 : ℤ) ^ (m + 2 + k / 3) ∣ fdiff k (F n (2 ^ (m + 1))) := by
  obtain ⟨r, e, he2, rfl⟩ : ∃ r e, e < 2 ∧ k = 2 * r + e :=
    ⟨k / 2, k % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 2).symm⟩
  rw [op_identity]
  change (2 : ℤ) ^ (m + 2 + (2 * r + e) / 3) ∣ ∑ i ∈ range (r + 1), T n m r e i
  rw [sum_range_succ']
  by_cases hr2 : r = 2
  · subst hr2
    have hk3 : (2 * 2 + e) / 3 = 1 := by omega
    rw [hk3]
    apply dvd_add
    · apply dvd_sum; intro i hi
      rw [mem_range] at hi
      exact (pow_dvd_pow 2 (by omega)).trans
        (T_bound n m 2 e (i + 1) 1 hn (by omega) (by omega) (by decide))
    · have := T_zero_bound n m 2 e hn
      have h2 : ((2 : ℤ) ^ (m + 2) * ((2 : ℕ).factorial : ℤ)) = 2 ^ (m + 2 + 1) := by
        norm_num [Nat.factorial]; ring
      rwa [h2] at this
  · have hineq : (2 * r + e) / 3 ≤ r / 2 + r / 4 + 1 := by omega
    have hs : 2 ^ ((2 * r + e) / 3 - 1) ∣ r.factorial :=
      (pow_dvd_pow 2 (Nat.sub_le_iff_le_add.mpr hineq)).trans (two_pow_fact4 r)
    apply dvd_add
    · apply dvd_sum; intro i hi
      rw [mem_range] at hi
      exact (pow_dvd_pow 2 (by omega)).trans
        (T_bound n m r e (i + 1) _ hn (by omega) (by omega) hs)
    · have h0 := T_zero_bound' n m r e hn he2 hr2
      have hs' : (2 : ℤ) ^ ((2 * r + e) / 3 - 1) ∣ (r.factorial : ℤ) := by exact_mod_cast hs
      refine dvd_trans ?_ h0
      refine dvd_trans (pow_dvd_pow 2 (show m + 2 + (2 * r + e) / 3 ≤
        (m + 3) + ((2 * r + e) / 3 - 1) by omega)) ?_
      rw [pow_add]
      exact mul_dvd_mul_left _ hs'

theorem two_E_diff (n m k : ℕ) (hn : m + 3 ≤ n) :
    (2 : ℤ) ^ (m + 2) ∣ E k (n + 2 ^ (m + 1)) - E k n := by
  have h1 : (2 : ℤ) ^ (k / 3) * 2 ^ (m + 2) ∣ 2 ^ (k / 3) * (E k (n + 2 ^ (m + 1)) - E k n) := by
    rw [mul_sub, E_spec, E_spec, D_sub_eq, ← pow_add, add_comm (k / 3)]
    exact lemmaB n m k hn
  exact (mul_dvd_mul_iff_left (by positivity)).mp h1

/-- Part 3: powers of two. -/
theorem A_two (n m : ℕ) (hn : m + 3 ≤ n) : (2 : ℤ) ^ (m + 2) ∣ A (n + 2 ^ (m + 1)) - A n := by
  rw [A_sub_eq]
  exact dvd_sum fun k _ => dvd_mul_of_dvd_right (two_E_diff n m k hn) _

end A370092
