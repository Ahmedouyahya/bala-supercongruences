import BalaProofs.TFFrob
import BalaProofs.TFEps
import BalaProofs.TFLift

/-!
# Theorem F (p ≥ 5), step 8 of PLAN-route-b.md: assembly

`theoremF`: `v_p(A(pM) - A(M)) ≥ 3 (1 + v_p M)` for all `M`, `p ≥ 5`, `a b : ℤ`, `c : ℕ`;
`tower_int`: the corresponding divisibility `p^{3k} ∣ s(n p^k) - s(n p^{k-1})` for any `s : ℕ → ℕ`
that agrees with `A a b c` on `N ≥ 1`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- **Theorem F** (p ≥ 5): `v_p(A(pM) - A(M)) ≥ 3 (1 + v_p M)` (for `M = 0` both sides are trivial). -/
theorem theoremF {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (a b : ℤ) (c M : ℕ) :
    V p (3 * (1 + (padicValNat p M : ℤ))) (A a b c (p * M) - A a b c M) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rw [A_sub hp2]
  apply V_sum
  intro w hw
  rw [mem_range] at hw
  set e := padicValNat p M with he
  have hpe : p ^ e ∣ M := pow_padicValNat_dvd
  have hN : p ^ (1 + e) ∣ p * M := by
    rw [pow_add, pow_one]
    exact mul_dvd_mul_left p hpe
  set K := c * M - w with hK
  have hK0 : K ≠ 0 := by omega
  have hT : c * M * p - p * w = p * K := by
    rw [hK, Nat.mul_sub, Nat.mul_comm p (c * M)]
  have hT0 : p * K ≠ 0 := mul_ne_zero hp0 hK0
  have hvT : padicValNat p (p * K) = 1 + padicValNat p K := by
    rw [padicValNat.mul hp0 hK0, padicValNat.self hp.out.one_lt]
  set τ := padicValNat p K with hτ
  rw [hT]
  by_cases hcase : e ≤ τ
  · -- τ ≥ r - 1: the ε-factor alone has valuation ≥ 3r
    have h1 := eps_bound (p := p) hp5 a b (N := p * M) (r := 1 + e) hN (by omega) hT0
      (dvd_mul_right p K) (k := 3 * ((1 + e : ℕ) : ℤ)) (by rw [hvT]; omega) le_rfl
    have h2 := pint_Phi (p := p) a b M w
    exact V_mono (V_mul h1 h2) (by omega)
  · -- τ ≤ r - 2: Lemma 6 for the φ^M-factor
    push_neg at hcase
    have h1 := eps_bound (p := p) hp5 a b (N := p * M) (r := 1 + e) hN (by omega) hT0
      (dvd_mul_right p K) (k := 2 * ((1 + e : ℕ) : ℤ) + (1 + τ)) (by rw [hvT]; omega)
      (by omega)
    have hw : ¬ p ^ (τ + 1) ∣ w := by
      intro hdvd
      have h3 : p ^ (τ + 1) ∣ c * M :=
        dvd_trans (pow_dvd_pow p (by omega : τ + 1 ≤ e)) (dvd_trans hpe (dvd_mul_left M c))
      have h4 : p ^ (τ + 1) ∣ K := by
        rw [hK]
        exact Nat.dvd_sub h3 hdvd
      exact pow_succ_padicValNat_not_dvd hK0 h4
    have h2 := lemma6 (pint_expS_F (p := p) a b) (t := τ + 1) (u := e - τ - 1) (M := M)
      (s := w) (by rw [show τ + 1 + (e - τ - 1) = e by omega]; exact hpe) hw
    rw [← Phi_eq_pow] at h2
    exact V_mono (V_mul h1 h2) (by omega)

/-- Theorem F as a divisibility statement for a sequence `s` agreeing with `A a b c` on `N ≥ 1`. -/
theorem tower_int {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℤ) (c : ℕ) (s : ℕ → ℕ)
    (hs : ∀ N, 1 ≤ N → (s N : ℚ) = A a b c N) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (p : ℤ) ^ (3 * k) ∣ (s (n * p ^ k) : ℤ) - (s (n * p ^ (k - 1)) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hM0 : n * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero)
  have hM1 : n * p ^ (j + 1) ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero)
  have hpM : n * p ^ (j + 1) = p * (n * p ^ j) := by ring
  have hF := theoremF (p := p) hp5 a b c (n * p ^ j)
  have hv : j ≤ padicValNat p (n * p ^ j) :=
    (padicValNat_dvd_iff_le hM0).mp (dvd_mul_left (p ^ j) n)
  have hV : V p ((3 * (j + 1) : ℕ) : ℤ)
      ((s (n * p ^ (j + 1)) : ℚ) - (s (n * p ^ j) : ℚ)) := by
    rw [hs _ (Nat.one_le_iff_ne_zero.mpr hM1), hs _ (Nat.one_le_iff_ne_zero.mpr hM0), hpM]
    exact V_mono hF (by omega)
  exact (V_int_iff_dvd (p := p) (3 * (j + 1))
    ((s (n * p ^ (j + 1)) : ℤ) - (s (n * p ^ j) : ℤ))).mp
    (by rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]; exact hV)

end

end TF
