import Mathlib

/-!
# `Γ(x + n) = Γ(x) ∏_{j < n} (x + j)` for real `x > 0`

Used to convert the Γ-quotients of the Formal Conjectures statements of A364175 and A364178 into
the integer forms of `notes/A364175-A364178-factorial-ratio-towers.md`:
`Γ(1 + n/2)/Γ(1 + 3n/2) = 2^n / ∏_{j=1}^{n} (n + 2j)` and
`Γ(1 + 2n/3)/Γ(1 + 5n/3) = 3^n / ∏_{j=1}^{n} (2n + 3j)`.
-/

open Finset

namespace Bala

theorem Gamma_add_nat_eq (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ j ∈ range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih]
    have hpos : x + n ≠ 0 := by positivity
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos]
    ring

end Bala
