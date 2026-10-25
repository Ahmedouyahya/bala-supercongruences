import BalaCheck.A376462First
import BalaCheck.A376462ShiftMain

/-!
# A376462: both conjectured supercongruences

`oeis_376462_conjecture_0` (Formal Conjectures, `FormalConjectures/OEIS/Auto/376462_96154f2f.lean`,
commit 67338a1) for all primes `p ≥ 5`, `n ≥ 1`, `r ≥ 1`: the first conjunct is `A376462_first`
(`BalaCheck/A376462First.lean`), the second is `A376462_shifted` (`BalaCheck/A376462ShiftMain.lean`).
-/

theorem A376462_from_target : type_of% @oeis_376462_conjecture_0 := by
  intro p n r hp hp5 hn hr
  exact ⟨A376462_first p n r hp hp5 hn hr, A376462_shifted p n r hp hp5 hn hr⟩
