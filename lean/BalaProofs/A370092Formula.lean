import Mathlib
import BalaProofs.A370092Defs

/-!
# A370092, Part 1: closed formula and integrality

`a n = Σ_{k ≤ n} g_k D(0,k,n)` where `D(c,k,n) = Σ_{j ≤ k} (-1)^(j+k) C(k,j) (j+c)^n` and
`G(u) = (1+u)/(1 - u² - u³/2) = Σ g_k u^k`; the integer form is `A n = Σ_k h_k · D(0,k,n)/2^⌊k/3⌋`.
-/

open Finset

namespace A370092

/- ### The target recurrence -/

theorem a_zero' : a 0 = 1 := by
  rw [a]

theorem a_succ (n : ℕ) : a (n + 1) = (-1 : ℚ) ^ (n + 1) + 1 / 2 * ∑ i ∈ range (n + 1),
    ((n + 1).choose (i + 1) : ℚ) * (1 - (-1 : ℚ) ^ (i + 1) - (-2 : ℚ) ^ (i + 1)) * a (n - i) := by
  rw [a]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right]

/- ### Finite differences -/

/-- `fdiff k f = Σ_{j ≤ k} (-1)^(j+k) C(k,j) f(j)`, the `k`-th forward difference of `f` at `0`. -/
def fdiff (k : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (j + k) * (k.choose j : ℤ) * f j

/-- `D c k n = Σ_{j ≤ k} (-1)^(j+k) C(k,j) (j+c)^n`. -/
def D (c : ℤ) (k n : ℕ) : ℤ := fdiff k (fun j => ((j : ℤ) + c) ^ n)

theorem D_zero_right (c : ℤ) (k : ℕ) : D c k 0 = if k = 0 then 1 else 0 := by
  unfold D fdiff
  simp only [pow_zero, mul_one]
  have : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (j + k) * (k.choose j : ℤ) =
      (-1) ^ k * ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℤ) := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [this, Int.alternating_sum_range_choose]
  split_ifs with hk <;> simp [hk]

theorem D_zero_left (c : ℤ) (n : ℕ) : D c 0 n = c ^ n := by
  simp [D, fdiff]

theorem D_succ (c : ℤ) (k n : ℕ) :
    D c (k + 1) (n + 1) = c * D c (k + 1) n + (k + 1) * D (c + 1) k n := by
  unfold D fdiff
  have h1 : ∀ j ∈ range (k + 1 + 1), (-1 : ℤ) ^ (j + (k + 1)) * ((k + 1).choose j : ℤ) *
      ((j : ℤ) + c) ^ (n + 1) = c * ((-1 : ℤ) ^ (j + (k + 1)) * ((k + 1).choose j : ℤ) *
      ((j : ℤ) + c) ^ n) + (-1 : ℤ) ^ (j + (k + 1)) * ((k + 1).choose j : ℤ) * (j : ℤ) *
      ((j : ℤ) + c) ^ n := by
    intro j _; ring
  rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]
  congr 1
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  refine sum_congr rfl fun i _ => ?_
  have hc : ((k + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((k : ℤ) + 1) * (k.choose i : ℤ) := by
    have := Nat.add_one_mul_choose_eq k i
    exact_mod_cast this.symm
  have hs : (-1 : ℤ) ^ (i + 1 + (k + 1)) = (-1) ^ (i + k) := by
    rw [show i + 1 + (k + 1) = i + k + 2 by ring, pow_add]; norm_num
  rw [hs]
  push_cast
  linear_combination ((-1 : ℤ) ^ (i + k) * ((i : ℤ) + (c + 1)) ^ n) * hc

theorem D_eq_zero (n : ℕ) : ∀ (c : ℤ) (k : ℕ), n < k → D c k n = 0 := by
  induction n with
  | zero => intro c k hk; rw [D_zero_right, if_neg (by omega)]
  | succ n ih =>
    intro c k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [D_succ, ih c (k + 1) (by omega), ih (c + 1) k (by omega)]; ring

theorem factorial_dvd_D (n : ℕ) : ∀ (c : ℤ) (k : ℕ), (k.factorial : ℤ) ∣ D c k n := by
  induction n with
  | zero =>
    intro c k; rw [D_zero_right]
    split_ifs with hk
    · subst hk; simp
    · simp
  | succ n ih =>
    intro c k
    cases k with
    | zero => simp
    | succ k =>
      rw [D_succ]
      apply dvd_add (dvd_mul_of_dvd_right (ih c (k + 1)) _)
      rw [Nat.factorial_succ, Nat.cast_mul]; push_cast
      exact mul_dvd_mul_left _ (ih (c + 1) k)

theorem D_pascal (c : ℤ) (k n : ℕ) : D (c + 1) k n = D c k n + D c (k + 1) n := by
  unfold D fdiff
  rw [sum_range_succ' _ (k + 1)]
  have hsplit : ∀ i ∈ range (k + 1), (-1 : ℤ) ^ (i + 1 + (k + 1)) * ((k + 1).choose (i + 1) : ℤ) *
      (((i + 1 : ℕ) : ℤ) + c) ^ n = (-1 : ℤ) ^ (i + k) * (k.choose i : ℤ) * ((i : ℤ) + (c + 1)) ^ n
        + (-1 : ℤ) ^ (i + k) * (k.choose (i + 1) : ℤ) * (((i + 1 : ℕ) : ℤ) + c) ^ n := by
    intro i _
    rw [Nat.choose_succ_succ', Nat.cast_add, show i + 1 + (k + 1) = i + k + 2 by ring, pow_add]
    push_cast; ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_range_succ (fun i => (-1 : ℤ) ^ (i + k) *
    (k.choose (i + 1) : ℤ) * (((i + 1 : ℕ) : ℤ) + c) ^ n) k, Nat.choose_succ_self,
    sum_range_succ' (fun j => (-1 : ℤ) ^ (j + k) * (k.choose j : ℤ) * ((j : ℤ) + c) ^ n) k]
  have hneg : ∀ i ∈ range k, (-1 : ℤ) ^ (i + k) * (k.choose (i + 1) : ℤ) *
      (((i + 1 : ℕ) : ℤ) + c) ^ n = -((-1 : ℤ) ^ (i + 1 + k) * (k.choose (i + 1) : ℤ) *
      (((i + 1 : ℕ) : ℤ) + c) ^ n) := by
    intro i _; rw [pow_add, pow_add, pow_add]; ring
  rw [sum_congr rfl hneg, sum_neg_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one, zero_add, pow_succ]
  ring

theorem D_conv (c : ℤ) (k n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℤ) * c ^ j * D 0 k (n - j) = D c k n := by
  unfold D fdiff
  simp only [add_zero]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [add_comm (i : ℤ) c, add_pow, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/- ### The coefficients `g_k` and `h_k = 2^⌊k/3⌋ g_k` -/

/-- Coefficients of `G(u) = (1+u)/(1 - u² - u³/2)`. -/
noncomputable def g : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | (k + 3) => g (k + 1) + g k / 2

/-- `h k = 2^⌊k/3⌋ g k`, integral. -/
def h : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | (k + 3) => (if k % 3 = 2 then 1 else 2) * h (k + 1) + h k

theorem g_rec (k : ℕ) : g (k + 3) = g (k + 1) + g k / 2 := by
  rw [g]

theorem h_eq (k : ℕ) : (h k : ℚ) = 2 ^ (k / 3) * g k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [h, g]
    | 1, _ => simp [h, g]
    | 2, _ => simp [h, g]
    | (k + 3), ih =>
      have ih1 := ih (k + 1) (by omega)
      have ih0 := ih k (by omega)
      rw [h, g_rec, show (k + 3) / 3 = k / 3 + 1 by omega]
      push_cast
      split_ifs with hk
      · rw [show (k + 1) / 3 = k / 3 + 1 by omega] at ih1
        rw [ih1, ih0]; ring
      · rw [show (k + 1) / 3 = k / 3 by omega] at ih1
        rw [ih1, ih0]; ring

/- ### The closed formula -/

/-- Rational closed form `Σ_{k ≤ n} g_k D(0,k,n)`. -/
noncomputable def Aq (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), g k * D 0 k n

theorem sum_range_extend {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n N : ℕ} (hnN : n ≤ N)
    (hf : ∀ k, n < k → f k = 0) : ∑ k ∈ range (n + 1), f k = ∑ k ∈ range (N + 1), f k := by
  rw [← sum_range_add_sum_Ico f (show n + 1 ≤ N + 1 by omega)]
  rw [sum_eq_zero (s := Ico (n + 1) (N + 1)) (fun k hk => hf k (by rw [mem_Ico] at hk; omega)),
    add_zero]

theorem Aq_conv (c : ℤ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (c : ℚ) ^ j * Aq (n - j) =
      ∑ k ∈ range (n + 1), g k * (D c k n : ℚ) := by
  have hext : ∀ j ∈ range (n + 1), Aq (n - j) = ∑ k ∈ range (n + 1), g k * (D 0 k (n - j) : ℚ) := by
    intro j hj
    unfold Aq
    exact sum_range_extend _ (by omega) (fun k hk => by rw [D_eq_zero _ _ _ hk]; simp)
  rw [sum_congr rfl (fun j hj => by rw [hext j hj])]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← D_conv c k n]
  push_cast
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

theorem four_term (k n : ℕ) : D 0 k n - D 1 k n + D (-1) k n + D (-2) k n =
    2 * D (-2) k n - 2 * D (-2) (k + 2) n - D (-2) (k + 3) n := by
  have h1 := D_pascal 0 k n
  have h2 := D_pascal (-1) k n
  have h3 := D_pascal (-1) (k + 1) n
  have h4 := D_pascal (-2) k n
  have h5 := D_pascal (-2) (k + 1) n
  have h6 := D_pascal (-2) (k + 2) n
  norm_num at h1 h2 h3 h4 h5 h6
  linarith

theorem tele (E : ℕ → ℚ) (N : ℕ) :
    ∑ k ∈ range (N + 3), g k * (2 * E k - 2 * E (k + 2) - E (k + 3)) =
      2 * E 0 + 2 * E 1 - 2 * g (N + 3) * E (N + 3) - (2 * g (N + 2) + g (N + 1)) * E (N + 4)
        - g (N + 2) * E (N + 5) := by
  induction N with
  | zero =>
    simp only [sum_range_succ, range_zero, sum_empty, zero_add]
    rw [g_rec 0]
    simp only [g]
    ring
  | succ N ih =>
    rw [show N + 1 + 3 = (N + 3) + 1 by ring, sum_range_succ, ih]
    have hg := g_rec (N + 1)
    rw [show N + 1 + 3 = N + 4 by ring] at hg
    rw [show N + 3 + 1 = N + 4 by ring, show N + 1 + 2 = N + 3 by ring,
      show N + 1 + 1 = N + 2 by ring, show N + 1 + 4 = N + 5 by ring,
      show N + 1 + 5 = N + 6 by ring, show N + 3 + 2 = N + 5 by ring,
      show N + 3 + 3 = N + 6 by ring, hg]
    ring

theorem Aq_identity (n : ℕ) :
    Aq n - ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) * Aq (n - j) =
      2 * (-1 : ℚ) ^ n := by
  have hsplit : ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) *
      Aq (n - j) = ∑ j ∈ range (n + 1), (n.choose j : ℚ) * ((1 : ℤ) : ℚ) ^ j * Aq (n - j)
        - ∑ j ∈ range (n + 1), (n.choose j : ℚ) * ((-1 : ℤ) : ℚ) ^ j * Aq (n - j)
        - ∑ j ∈ range (n + 1), (n.choose j : ℚ) * ((-2 : ℤ) : ℚ) ^ j * Aq (n - j) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by push_cast; ring
  rw [hsplit, Aq_conv, Aq_conv, Aq_conv]
  have key : Aq n - (∑ k ∈ range (n + 1), g k * (D 1 k n : ℚ) -
      ∑ k ∈ range (n + 1), g k * (D (-1) k n : ℚ) - ∑ k ∈ range (n + 1), g k * (D (-2) k n : ℚ))
      = ∑ k ∈ range (n + 1), g k * (2 * (D (-2) k n : ℚ) - 2 * D (-2) (k + 2) n
          - D (-2) (k + 3) n) := by
    unfold Aq
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    have hq : ((D 0 k n - D 1 k n + D (-1) k n + D (-2) k n : ℤ) : ℚ) =
        ((2 * D (-2) k n - 2 * D (-2) (k + 2) n - D (-2) (k + 3) n : ℤ) : ℚ) := by
      rw [four_term]
    push_cast at hq
    linear_combination g k * hq
  rw [key, sum_range_extend (fun k => g k * (2 * (D (-2) k n : ℚ) - 2 * D (-2) (k + 2) n
      - D (-2) (k + 3) n)) (show n ≤ n + 2 by omega) (fun k hk => by
        simp [D_eq_zero n _ k hk, D_eq_zero n _ (k + 2) (by omega),
          D_eq_zero n _ (k + 3) (by omega)])]
  rw [show n + 2 + 1 = n + 3 by ring, tele (fun s => (D (-2) s n : ℚ)) n]
  simp only [D_eq_zero n _ (n + 3) (by omega), D_eq_zero n _ (n + 4) (by omega),
    D_eq_zero n _ (n + 5) (by omega)]
  simp [D, fdiff, sum_range_succ]
  ring

theorem Aq_succ (n : ℕ) : Aq (n + 1) = (-1 : ℚ) ^ (n + 1) + 1 / 2 * ∑ i ∈ range (n + 1),
    ((n + 1).choose (i + 1) : ℚ) * (1 - (-1 : ℚ) ^ (i + 1) - (-2 : ℚ) ^ (i + 1)) * Aq (n - i) := by
  have := Aq_identity (n + 1)
  rw [sum_range_succ'] at this
  simp only [Nat.add_sub_add_right, Nat.choose_zero_right, pow_zero, Nat.sub_zero,
    Nat.cast_one] at this
  linear_combination this / 2

theorem a_eq_Aq (n : ℕ) : a n = Aq n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [a_zero']; simp [Aq, D, fdiff, g]
    | succ n =>
      rw [a_succ, Aq_succ]
      congr 2
      refine sum_congr rfl fun i hi => ?_
      rw [ih (n - i) (by omega)]

/- ### Integrality -/

theorem two_pow_half_dvd_factorial (k : ℕ) : 2 ^ (k / 2) ∣ k.factorial := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (k + 2), ih =>
      have ih0 := ih k (by omega)
      rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ, Nat.factorial_succ, Nat.factorial_succ,
        ← mul_assoc, mul_comm (2 ^ (k / 2)) 2]
      refine mul_dvd_mul ?_ ih0
      have := (Nat.even_mul_succ_self (k + 1)).two_dvd
      rwa [mul_comm] at this

theorem two_pow_dvd_D (k n : ℕ) : (2 : ℤ) ^ (k / 3) ∣ D 0 k n := by
  have h1 : (2 : ℤ) ^ (k / 3) ∣ (2 : ℤ) ^ (k / 2) := pow_dvd_pow 2 (by omega)
  have h2 : (2 : ℤ) ^ (k / 2) ∣ (k.factorial : ℤ) := by exact_mod_cast two_pow_half_dvd_factorial k
  exact h1.trans (h2.trans (factorial_dvd_D n 0 k))

/-- `E k n = D(0,k,n) / 2^⌊k/3⌋` (exact). -/
def E (k n : ℕ) : ℤ := D 0 k n / 2 ^ (k / 3)

theorem E_spec (k n : ℕ) : 2 ^ (k / 3) * E k n = D 0 k n := by
  exact Int.mul_ediv_cancel' (two_pow_dvd_D k n)

/-- Integer closed form. -/
def A (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), h k * E k n

theorem A_cast (n : ℕ) : (A n : ℚ) = Aq n := by
  unfold A Aq
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [h_eq, ← E_spec k n]
  push_cast; ring

theorem a_eq_A (n : ℕ) : a n = A n := by
  rw [a_eq_Aq, A_cast]

theorem a_num (n : ℕ) : (a n).num = A n := by
  rw [a_eq_A]; exact Rat.num_intCast _

/- ### Shared lemmas for Parts 2 and 3 -/

theorem fdiff_add (k : ℕ) (f f' : ℕ → ℤ) :
    fdiff k (fun j => f j + f' j) = fdiff k f + fdiff k f' := by
  unfold fdiff; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring

theorem fdiff_sub (k : ℕ) (f f' : ℕ → ℤ) :
    fdiff k (fun j => f j - f' j) = fdiff k f - fdiff k f' := by
  unfold fdiff; rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring

theorem fdiff_const_mul (k : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    fdiff k (fun j => c * f j) = c * fdiff k f := by
  unfold fdiff; rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

theorem fdiff_dvd (k : ℕ) (f : ℕ → ℤ) (q : ℤ) (hf : ∀ j, q ∣ f j) : q ∣ fdiff k f :=
  dvd_sum fun j _ => dvd_mul_of_dvd_right (hf j) _

/-- `b_k = D(0,k,n+P) - D(0,k,n) = fdiff k (j ↦ j^n (j^P - 1))`. -/
theorem D_sub_eq (k n P : ℕ) :
    D 0 k (n + P) - D 0 k n = fdiff k (fun j => (j : ℤ) ^ n * ((j : ℤ) ^ P - 1)) := by
  unfold D fdiff
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [add_zero]; ring

theorem A_sub_eq (n P : ℕ) :
    A (n + P) - A n = ∑ k ∈ range (n + P + 1), h k * (E k (n + P) - E k n) := by
  unfold A
  rw [sum_range_extend (fun k => h k * E k n) (show n ≤ n + P by omega)
    (fun k hk => by simp [E, D_eq_zero n 0 k hk])]
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by ring

end A370092
