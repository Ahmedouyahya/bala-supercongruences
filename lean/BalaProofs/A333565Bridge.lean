import Mathlib
import Mathlib
import BalaProofs.A333565Defs

/-!
Bridge identities for OEIS A333565 (target `FormalConjectures/OEIS/Auto/333565_757e3efd.lean`).

With `B n = Σ_{k=0}^{n} C(2n, n-k) C(n+k-1, k)` for `n ≥ 1` and `B 0 = 1`:
`A333565 n = 2 B(n) - (-1)^n` (as integers).

`BalaCheck.A333562Ident` cannot be imported together with the A333565 target module (both target
modules declare the root names `a_zero … a_three`), so its binomial lemmas `f, D, G, S, R, cert, D_rec,
D_closed, R_succ, S_eq_R` are reproduced below verbatim (they are re-checked here).
-/

open Finset

namespace A333565

/- ### Copied from `BalaCheck/A333562Ident.lean` (namespace `A333562`); `n = m + 1` -/

/-- summand `f(K,i) = C(m+K, K-i) C(m+i, i)` -/
def f (m K i : ℕ) : ℕ := (m + K).choose (K - i) * (m + i).choose i

/-- `D(m+1, K) = Σ_{i=0}^{K} C(m+K, K-i) C(m+i, i)` -/
def D (m K : ℕ) : ℕ := ∑ i ∈ range (K + 1), f m K i

/-- certificate `G(K,i) = i C(m+K+1, K+1-i) C(m+i, i)` (in `ℤ`) -/
def G (m K i : ℕ) : ℤ := (i : ℤ) * ((m + K + 1).choose (K + 1 - i) : ℤ) * ((m + i).choose i : ℤ)

/-- `S(m+1, K) = Σ_{j=0}^{K} C(m+j, j) 2^j` -/
def S (m K : ℕ) : ℕ := ∑ j ∈ range (K + 1), (m + j).choose j * 2 ^ j

/-- `R(m+1, K) = Σ_{k=0}^{K} C(m+1+K, K-k) C(m+k, k)` -/
def R (m K : ℕ) : ℕ := ∑ k ∈ range (K + 1), (m + 1 + K).choose (K - k) * (m + k).choose k

/-- the Zeilberger certificate identity, for `i ≤ K` -/
theorem cert (m K i : ℕ) (hi : i ≤ K) :
    2 * ((m : ℤ) + K + 1) * (f m K i : ℤ) - ((K : ℤ) + 1) * (f m (K + 1) i : ℤ)
      = G m K (i + 1) - G m K i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  unfold f G
  rw [show i + j - i = j by omega, show i + j + 1 - i = j + 1 by omega,
    show i + j + 1 - (i + 1) = j by omega, show m + (i + j + 1) = m + (i + j) + 1 by omega,
    show m + (i + 1) = m + i + 1 by omega]
  have h1 := Nat.add_one_mul_choose_eq (m + (i + j)) j
  have h2 := Nat.choose_mul_succ_eq (m + (i + j)) j
  rw [show m + (i + j) + 1 - j = m + i + 1 by omega] at h2
  have h3 := Nat.add_one_mul_choose_eq (m + i) i
  have h1' : (((m + (i + j) + 1 : ℕ) : ℤ)) * ((m + (i + j)).choose j : ℤ)
      = ((m + (i + j) + 1).choose (j + 1) : ℤ) * (((j + 1 : ℕ)) : ℤ) := by exact_mod_cast h1
  have h2' : ((m + (i + j)).choose j : ℤ) * (((m + (i + j) + 1 : ℕ) : ℤ))
      = ((m + (i + j) + 1).choose j : ℤ) * (((m + i + 1 : ℕ)) : ℤ) := by exact_mod_cast h2
  have h3' : (((m + i + 1 : ℕ) : ℤ)) * ((m + i).choose i : ℤ)
      = ((m + i + 1).choose (i + 1) : ℤ) * (((i + 1 : ℕ)) : ℤ) := by exact_mod_cast h3
  push_cast at h1' h2' h3' ⊢
  linear_combination ((m + i).choose i : ℤ) * h1' + ((m + i).choose i : ℤ) * h2'
    + ((m + (i + j) + 1).choose j : ℤ) * h3'

/-- the recurrence `(K+1) D(K+1) = 2(m+K+1) D(K)` obtained by telescoping -/
theorem D_rec (m K : ℕ) : (K + 1) * D m (K + 1) = 2 * (m + K + 1) * D m K := by
  have hsum : ∑ i ∈ range (K + 1), (2 * ((m : ℤ) + K + 1) * (f m K i : ℤ)
      - ((K : ℤ) + 1) * (f m (K + 1) i : ℤ)) = G m K (K + 1) - G m K 0 := by
    rw [← Finset.sum_range_sub]
    apply Finset.sum_congr rfl
    intro i hi
    exact cert m K i (by simp at hi; omega)
  have hG0 : G m K 0 = 0 := by simp [G]
  have hGK : G m K (K + 1) = ((K : ℤ) + 1) * ((m + (K + 1)).choose (K + 1) : ℤ) := by
    unfold G
    rw [Nat.sub_self, Nat.choose_zero_right]
    push_cast
    ring
  have hD1 : (D m (K + 1) : ℤ)
      = ∑ i ∈ range (K + 1), (f m (K + 1) i : ℤ) + ((m + (K + 1)).choose (K + 1) : ℤ) := by
    unfold D
    rw [Finset.sum_range_succ]
    push_cast
    congr 1
    unfold f
    rw [Nat.sub_self, Nat.choose_zero_right]
    push_cast
    ring
  have hD : (D m K : ℤ) = ∑ i ∈ range (K + 1), (f m K i : ℤ) := by
    unfold D
    push_cast
    rfl
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hG0, hGK] at hsum
  have key : ((K : ℤ) + 1) * (D m (K + 1) : ℤ) = 2 * ((m : ℤ) + K + 1) * (D m K : ℤ) := by
    rw [hD1, hD]
    linear_combination (-1 : ℤ) * hsum
  exact_mod_cast key

/-- item 1: `Σ_{i=0}^{K} C(n+K-1, K-i) C(n+i-1, i) = 2^K C(n+K-1, K)` with `n = m+1` -/
theorem D_closed (m K : ℕ) : D m K = 2 ^ K * (m + K).choose K := by
  induction K with
  | zero => simp [D, f]
  | succ K ih =>
    have h1 := D_rec m K
    have h2 := Nat.add_one_mul_choose_eq (m + K) K
    rw [ih] at h1
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < K + 1)
    rw [h1, show m + (K + 1) = m + K + 1 by omega]
    calc 2 * (m + K + 1) * (2 ^ K * (m + K).choose K)
        = 2 ^ (K + 1) * ((m + K + 1) * (m + K).choose K) := by ring
      _ = 2 ^ (K + 1) * ((m + K + 1).choose (K + 1) * (K + 1)) := by rw [h2]
      _ = (K + 1) * (2 ^ (K + 1) * (m + K + 1).choose (K + 1)) := by ring

/-- `R(K+1) = R(K) + D(K+1)` (Pascal's rule) -/
theorem R_succ (m K : ℕ) : R m (K + 1) = R m K + D m (K + 1) := by
  have e1 : R m (K + 1) = (∑ k ∈ range (K + 1), (m + 1 + (K + 1)).choose (K + 1 - k)
      * (m + k).choose k) + (m + (K + 1)).choose (K + 1) := by
    unfold R
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.choose_zero_right, one_mul]
  have e2 : D m (K + 1) = (∑ k ∈ range (K + 1), (m + (K + 1)).choose (K + 1 - k)
      * (m + k).choose k) + (m + (K + 1)).choose (K + 1) := by
    unfold D f
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.choose_zero_right, one_mul]
  have hsplit : ∑ k ∈ range (K + 1), (m + 1 + (K + 1)).choose (K + 1 - k) * (m + k).choose k
      = R m K + ∑ k ∈ range (K + 1), (m + (K + 1)).choose (K + 1 - k) * (m + k).choose k := by
    unfold R
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ K := by simp at hk; omega
    rw [show K + 1 - k = (K - k) + 1 by omega, show m + 1 + (K + 1) = (m + 1 + K) + 1 by omega,
      Nat.choose_succ_succ', show m + (K + 1) = m + 1 + K by omega]
    ring
  rw [e1, e2, hsplit]
  ring

/-- item 2: `S(n,K) = R(n,K)` with `n = m+1` -/
theorem S_eq_R (m K : ℕ) : S m K = R m K := by
  induction K with
  | zero => simp [S, R]
  | succ K ih =>
    rw [R_succ, ← ih, D_closed]
    unfold S
    rw [Finset.sum_range_succ _ (K + 1)]
    ring

/- ### The bridge -/

/-- `B n = Σ_{k=0}^{n} C(2n, n-k) C(n+k-1, k)` for `n ≥ 1`, and `B 0 = 1`. -/
def B : ℕ → ℕ
  | 0 => 1
  | (m + 1) => ∑ k ∈ range (m + 1 + 1), Nat.choose (2 * (m + 1)) (m + 1 - k)
      * Nat.choose (m + 1 + k - 1) k

/-- the pieces of the target definition, as top-level functions -/
def bz (m : ℕ) : ℤ := (2 ^ m * (2 * m).choose m : ℕ)

def dz (i : ℕ) : ℤ := (Finset.range (i + 1)).sum fun k => (-1 : ℤ) ^ k * bz (i - k)

def ez (n : ℕ) : ℤ := dz n + 4 * if n = 0 then 0 else dz (n - 1)

theorem A333565_eq_toNat (n : ℕ) : A333565 n = (ez n).toNat := rfl

theorem B_eq_coeffForm (n : ℕ) (hn : 1 ≤ n) :
    B n = ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n) (n - k) * Nat.choose (n + k - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem B_succ_eq_R (m : ℕ) : B (m + 1) = R m (m + 1) := by
  show ∑ k ∈ range (m + 1 + 1), Nat.choose (2 * (m + 1)) (m + 1 - k)
      * Nat.choose (m + 1 + k - 1) k
    = ∑ k ∈ range (m + 1 + 1), (m + 1 + (m + 1)).choose (m + 1 - k) * (m + k).choose k
  apply Finset.sum_congr rfl
  intro k _
  rw [show 2 * (m + 1) = m + 1 + (m + 1) by ring, show m + 1 + k - 1 = m + k by omega]

theorem B_succ_eq_S (m : ℕ) : B (m + 1) = S m (m + 1) := by
  rw [B_succ_eq_R, S_eq_R]

theorem B_pos (n : ℕ) : 1 ≤ B n := by
  cases n with
  | zero => simp [B]
  | succ m =>
    rw [B_succ_eq_S]
    unfold S
    rw [Finset.sum_range_succ']
    have h0 : (m + 0).choose 0 * 2 ^ 0 = 1 := by simp
    rw [h0]
    omega

/-- Pascal: `S(n,K) = S(n-1,K) + 2 S(n,K-1)` with `n = m + 2`, `K = K + 1` -/
theorem S_pascal (m K : ℕ) : S (m + 1) (K + 1) = S m (K + 1) + 2 * S (m + 1) K := by
  have h : ∀ j, (m + 1 + (j + 1)).choose (j + 1) * 2 ^ (j + 1)
      = (m + (j + 1)).choose (j + 1) * 2 ^ (j + 1) + 2 * ((m + 1 + j).choose j * 2 ^ j) := by
    intro j
    rw [show m + 1 + (j + 1) = m + (j + 1) + 1 by omega, Nat.choose_succ_succ',
      show m + (j + 1) = m + 1 + j by omega, pow_succ]
    ring
  unfold S
  rw [Finset.sum_range_succ' _ (K + 1), Finset.sum_range_succ' _ (K + 1)]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Nat.choose_zero_right, Nat.choose_zero_right]
  ring

/-- `2 (B(m+1) + B(m)) = b(m+1) + 4 b(m)` -/
theorem B_add (m : ℕ) : 2 * (B (m + 1) + B m)
    = 2 ^ (m + 1) * (2 * (m + 1)).choose (m + 1) + 4 * (2 ^ m * (2 * m).choose m) := by
  cases m with
  | zero => decide
  | succ m =>
    rw [B_succ_eq_S, B_succ_eq_S]
    have hP : S (m + 1) (m + 1 + 1) = S m (m + 1 + 1) + 2 * S (m + 1) (m + 1) :=
      S_pascal m (m + 1)
    have e1 : S m (m + 1 + 1)
        = S m (m + 1) + (m + (m + 1 + 1)).choose (m + 1 + 1) * 2 ^ (m + 1 + 1) := by
      unfold S
      rw [Finset.sum_range_succ]
    have e2 : S (m + 1) (m + 1 + 1)
        = S (m + 1) (m + 1) + (m + 1 + (m + 1 + 1)).choose (m + 1 + 1) * 2 ^ (m + 1 + 1) := by
      unfold S
      rw [Finset.sum_range_succ]
    have h3 : (m + 1 + (m + 1 + 1)).choose (m + 1 + 1)
        = (2 * (m + 1)).choose (m + 1) + (m + (m + 1 + 1)).choose (m + 1 + 1) := by
      rw [show m + 1 + (m + 1 + 1) = 2 * (m + 1) + 1 by ring, Nat.choose_succ_succ',
        show 2 * (m + 1) = m + (m + 1 + 1) by ring]
    have hs : (m + 1 + (m + 1 + 1)).choose (m + 1) = (m + 1 + (m + 1 + 1)).choose (m + 1 + 1) :=
      Nat.choose_symm_of_eq_add rfl
    have h4 : (2 * (m + 1 + 1)).choose (m + 1 + 1) = 2 * (m + 1 + (m + 1 + 1)).choose (m + 1 + 1) := by
      rw [show 2 * (m + 1 + 1) = m + 1 + (m + 1 + 1) + 1 by ring, Nat.choose_succ_succ', hs]
      ring
    zify at hP e1 e2 h3 h4 ⊢
    linear_combination (-2 : ℤ) * hP - 2 * e1 + 4 * e2 + 2 * (2 : ℤ) ^ (m + 1 + 1) * h3
      - (2 : ℤ) ^ (m + 1 + 1) * h4

theorem d_succ (n : ℕ) : dz (n + 1) + dz n = bz (n + 1) := by
  have h : ∀ k, (-1 : ℤ) ^ (k + 1) * bz (n + 1 - (k + 1)) = -((-1) ^ k * bz (n - k)) := by
    intro k
    rw [Nat.add_sub_add_right, pow_succ]
    ring
  unfold dz
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [h, Finset.sum_neg_distrib, pow_zero, one_mul, Nat.sub_zero]
  ring

theorem e_add (n : ℕ) : ez (n + 1) + ez n = bz (n + 1) + 4 * bz n := by
  rcases n with _ | n
  · show ez 1 + ez 0 = bz 1 + 4 * bz 0
    have h1 : dz 1 + dz 0 = bz 1 := d_succ 0
    have h0 : dz 0 = bz 0 := by simp [dz]
    have ha : ez 1 = dz 1 + 4 * dz 0 := by
      unfold ez
      rw [if_neg (show (1 : ℕ) ≠ 0 by omega)]
    have hb : ez 0 = dz 0 := by
      unfold ez
      rw [if_pos rfl]
      ring
    rw [ha, hb]
    linear_combination h1 + 4 * h0
  · show ez (n + 2) + ez (n + 1) = bz (n + 2) + 4 * bz (n + 1)
    have h1 : dz (n + 2) + dz (n + 1) = bz (n + 2) := d_succ (n + 1)
    have h2 : dz (n + 1) + dz n = bz (n + 1) := d_succ n
    have ha : ez (n + 2) = dz (n + 2) + 4 * dz (n + 1) := by
      unfold ez
      rw [if_neg (show n + 2 ≠ 0 by omega), show n + 2 - 1 = n + 1 by omega]
    have hb : ez (n + 1) = dz (n + 1) + 4 * dz n := by
      unfold ez
      rw [if_neg (show n + 1 ≠ 0 by omega), Nat.add_sub_cancel]
    rw [ha, hb]
    linear_combination h1 + 4 * h2

theorem e_eq (n : ℕ) : ez n = 2 * (B n : ℤ) - (-1) ^ n := by
  induction n with
  | zero => norm_num [ez, dz, bz, B]
  | succ n ih =>
    have h1 := e_add n
    have h2 : (2 : ℤ) * ((B (n + 1) : ℤ) + (B n : ℤ)) = bz (n + 1) + 4 * bz n := by
      unfold bz
      exact_mod_cast B_add n
    rw [pow_succ]
    linear_combination h1 - ih - h2

theorem A333565_eq (n : ℕ) : (A333565 n : ℤ) = 2 * (B n : ℤ) - (-1) ^ n := by
  have he := e_eq n
  have hB : (1 : ℤ) ≤ (B n : ℤ) := by exact_mod_cast B_pos n
  have hnn : 0 ≤ ez n := by
    rw [he]
    rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] <;> linarith
  rw [A333565_eq_toNat, Int.toNat_of_nonneg hnn, he]

theorem A333565_diff (N M : ℕ) (h : Even N ↔ Even M) :
    (A333565 N : ℤ) - A333565 M = 2 * ((B N : ℤ) - B M) := by
  have hpow : (-1 : ℤ) ^ N = (-1) ^ M := by
    rcases Nat.even_or_odd N with hN | hN
    · rw [hN.neg_one_pow, (h.1 hN).neg_one_pow]
    · have hM : Odd M := Nat.not_even_iff_odd.1 (fun hM => (Nat.not_even_iff_odd.2 hN) (h.2 hM))
      rw [hN.neg_one_pow, hM.neg_one_pow]
  rw [A333565_eq, A333565_eq, hpow]
  ring

end A333565
