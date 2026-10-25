import Mathlib

/-!
Lemma 2 of `notes/A361711-proof.md` in product form (milestone M3).

For `M = p·M'` with `p` and `M'` odd, `n = (M-1)/2`, `n' = (M'-1)/2` and any `g : ℚ → ℚ`,

  `∏_{i=1}^{n} g(M/i) = (∏_{u ∈ U} g(M/u)) · ∏_{i=1}^{n'} g(M'/i)`,   `U = {u ∈ [1,n] : p ∤ u}`.

Applied with `g x = 1 - x^2` this is `(E1)·(E2)` of the note.
Also the product formulas `(-1)^n C(2n,n) = ∏_{i<n} (1 - (2n+1)/(i+1))` and
`C(3n+1,n) = ∏_{i<n} (1 + (2n+1)/(i+1))`.
-/

open Finset

namespace Bala

/-- the multiples of `p` in `[1, p*n'+q]` (with `q < p`) are the `p*i'` with `i' ∈ [1, n']` -/
theorem filter_dvd_Icc (p n' q : ℕ) (hq : q < p) :
    (Icc 1 (p * n' + q)).filter (fun i => p ∣ i) = (Icc 1 n').image (fun i => p * i) := by
  ext x
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨i, rfl⟩⟩
    refine ⟨i, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos i with rfl | h
      · omega
      · exact h
    · by_contra hcon
      push_neg at hcon
      have h3 : p * (n' + 1) ≤ p * i := Nat.mul_le_mul_left p hcon
      have h4 : p * (n' + 1) = p * n' + p := Nat.mul_succ p n'
      omega
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p i⟩
    · have : 0 < p * i := Nat.mul_pos (by omega) h1
      omega
    · have : p * i ≤ p * n' := Nat.mul_le_mul_left p h2
      omega

/-- The splitting lemma. -/
theorem prod_split (p M' n n' : ℕ) (hp : Odd p) (hM' : M' = 2 * n' + 1) (hn : p * M' = 2 * n + 1)
    (g : ℚ → ℚ) :
    ∏ i ∈ Icc 1 n, g (((p * M' : ℕ) : ℚ) / (i : ℚ))
      = (∏ u ∈ (Icc 1 n).filter (fun u => ¬ p ∣ u), g (((p * M' : ℕ) : ℚ) / (u : ℚ)))
        * ∏ i ∈ Icc 1 n', g ((M' : ℚ) / (i : ℚ)) := by
  obtain ⟨q, hq⟩ := hp
  have hnn : n = p * n' + q := by
    have : p * M' = 2 * (p * n' + q) + 1 := by
      rw [hM', hq]
      ring
    omega
  have hp0 : (p : ℚ) ≠ 0 := by
    have : 0 < p := by omega
    exact_mod_cast this.ne'
  rw [← prod_filter_mul_prod_filter_not (Icc 1 n) (fun i => p ∣ i)]
  conv_lhs => rw [mul_comm]
  congr 1
  rw [hnn, filter_dvd_Icc p n' q (by omega)]
  have hinj : Set.InjOn (fun i => p * i) ↑(Icc 1 n') := by
    intro x _ y _ hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  rw [prod_image hinj]
  apply prod_congr rfl
  intro i _
  congr 1
  push_cast
  rw [mul_div_mul_left _ _ hp0]

/-- `∏_{i ∈ range n} (1 - (2n+1)/(i+1)) = (-1)^n C(2n, n)` -/
theorem prod_one_sub_eq_choose (n : ℕ) :
    ∏ i ∈ range n, (1 - ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1)) = (-1) ^ n * ((2 * n).choose n : ℚ) := by
  have h1 : ∀ i ∈ range n,
      (1 - ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1))
        = (-1) * (((2 * n - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) := by
    intro i hi
    have hi' : i < n := mem_range.mp hi
    rw [Nat.cast_sub (by omega)]
    push_cast
    have : (i : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range, prod_div_distrib,
    ← Nat.cast_prod, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    prod_range_add_one_eq_factorial, Nat.descFactorial_eq_factorial_mul_choose]
  have hf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  push_cast
  field_simp
  try ring

/-- `∏_{i ∈ range n} (1 + (2n+1)/(i+1)) = C(3n+1, n)` -/
theorem prod_one_add_eq_choose (n : ℕ) :
    ∏ i ∈ range n, (1 + ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1)) = ((3 * n + 1).choose n : ℚ) := by
  have h1 : ∀ i ∈ range n,
      (1 + ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1))
        = (((2 * n + 2 + i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) := by
    intro i _
    push_cast
    have : (i : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [prod_congr rfl h1, prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.ascFactorial_eq_prod_range, prod_range_add_one_eq_factorial]
  have h2 : (2 * n + 2).ascFactorial n = n.factorial * (3 * n + 1).choose n := by
    have := Nat.ascFactorial_eq_factorial_mul_choose (2 * n + 1) n
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, show 2 * n + 1 + n = 3 * n + 1 by ring] at this
    exact this
  rw [h2]
  have hf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  push_cast
  field_simp
  try ring

/-- products over `Icc 1 n` versus products over `range n` -/
theorem prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Icc 1 n, f i = ∏ i ∈ range n, f (i + 1) := by
  have : Icc 1 n = Ico 1 (n + 1) := by
    ext i
    simp only [mem_Icc, mem_Ico]
    omega
  rw [this, prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  apply prod_congr rfl
  intro i _
  rw [add_comm]

end Bala
