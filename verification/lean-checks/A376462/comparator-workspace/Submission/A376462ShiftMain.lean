import Submission.A376462ShiftJ
import Submission.A376462ShiftB
import Submission.A376462ShiftS

/-!
# A376462: the second (shifted) conjectured supercongruence

The statement is the second conjunct of `oeis_376462_conjecture_0` in the Formal Conjectures file
`FormalConjectures/OEIS/Auto/376462_96154f2f.lean` (commit 67338a1), whose definitions
`A376462`, `a108625_aux` are imported unchanged.

Proof (`proofs/A376462-shifted-congruence.md`; `N = m p^r`, `M = m p^(r-1)`): representation
`a(N-1) = Σ_{k,j<N} S̃(N;k,j)` and the class split (`split4`), then the four classes
`classS` (§7), `classJ` (§5), `classK` (§4), `classB` (§6), all in `ℤ_[p]`, transferred to `ℤ`.
-/

open Nat Finset

namespace A376462Shift

/-- `p^(3r) ∣ a(m p^r - 1) - a(m p^(r-1) - 1)` in `ℤ_[p]` (`r = w + 1`). -/
theorem shift_padic (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (m w : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ((A376462 (m * p ^ (w + 1) - 1) : ℕ) : ℤ_[p])
      - ((A376462 (m * p ^ w - 1) : ℕ) : ℤ_[p]) := by
  rw [split4 p m w hm]
  exact dvd_add (dvd_add (dvd_add (classS p hp5 m w hm) (classJ p hp5 m w hm))
    (classK p hp5 m w hm)) (classB p hp5 m w hm)

end A376462Shift

theorem A376462_shifted : ∀ (p n r : ℕ), Nat.Prime p → 5 ≤ p → 0 < n → 0 < r →
    (A376462 (n * p ^ r - 1) : ℤ) ≡ (A376462 (n * p ^ (r - 1) - 1) : ℤ)
      [ZMOD (p ^ (3 * r) : ℕ).cast] := by
  intro p n r hp hp5 hn hr
  haveI := Fact.mk hp
  obtain ⟨w, rfl⟩ : ∃ w, r = w + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  push_cast
  rw [A386548.int_dvd_iff_padic_dvd p]
  push_cast
  exact A376462Shift.shift_padic p hp5 n w hn
