import BalaCheck.TFMain
import BalaCheck.TFInst
import BalaCheck.BinomIdent

/-!
Bala's conjecture on A333561 for the sequence as DEFINED on the OEIS, a(n) = Σ_{j=0..2n} C(n+j−1, j)·2^j.
(The benchmark target uses the equivalent formula Σ_{k≤2n} C(3n, 2n−k)·C(n+k−1, k); `A333561.lean` proves the
target. Here the OEIS definition is linked to Theorem F by the identity of `BinomIdent` with K = 2n.)
-/

open Finset

namespace A333561Oeis

/-- A333561 as defined on the OEIS: a(n) = Σ_{j = 0..2n} binomial(n+j−1, j)·2^j. -/
def aOEIS (n : ℕ) : ℕ := ∑ j ∈ range (2 * n + 1), (n + j - 1).choose j * 2 ^ j

theorem aOEIS_eq_rep (N : ℕ) (hN : 1 ≤ N) :
    aOEIS N = ∑ k ∈ range (2 * N + 1), Nat.choose (3 * N) (2 * N - k) * Nat.choose (N + k - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hS : aOEIS (m + 1) = BinomIdent.S m (2 * (m + 1)) := by
    unfold aOEIS BinomIdent.S
    apply Finset.sum_congr rfl
    intro j _
    rw [show m + 1 + j - 1 = m + j by omega]
  rw [hS, BinomIdent.S_eq_R]
  unfold BinomIdent.R
  apply Finset.sum_congr rfl
  intro k _
  rw [show m + 1 + 2 * (m + 1) = 3 * (m + 1) by ring, show m + 1 + k - 1 = m + k by omega]

/-- Bala's conjecture on A333561, for the OEIS definition. -/
theorem aOEIS_supercongruence :
    ∀ (p n k : ℕ), Nat.Prime p → p ≥ 5 → n ≥ 1 → k ≥ 1 →
      aOEIS (n * p ^ k) ≡ aOEIS (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  have h := TF.tower_int hp hp5 ((3 : ℕ) : ℤ) (-1) 2 aOEIS
    (fun N hN => by rw [TF.A_m_neg_one 3 2 N hN, aOEIS_eq_rep N hN]) hn hk
  exact_mod_cast h

end A333561Oeis
