import BalaProofs.TFSetup

/-!
# Theorem F, step 7 of PLAN-route-b.md: Frobenius lifting (Lemmas 5–6)

For `G` with `p`-integral coefficients: `G^{p^t} ≡ H (mod p)` with `H` supported on multiples of `p^t`;
lifting `X ≡ Y (mod p^k) ⇒ X^p ≡ Y^p (mod p^{k+1})`; hence, if `p^{t+u} ∣ M` and `p^t ∤ s`, then
`v_p([x^s] G^M) ≥ u + 1`.
-/

namespace TF

open PowerSeries Finset Epoch333042.Super

noncomputable section

/-- coefficientwise congruence modulo `p^k`. -/
def Cong (p : ℕ) (k : ℤ) (G H : ℚ⟦X⟧) : Prop := ∀ j, V p k (coeff j (G - H))

/-- `H` is supported on exponents divisible by `p^t`. -/
def Sparse (p t : ℕ) (H : ℚ⟦X⟧) : Prop := ∀ j, ¬ p ^ t ∣ j → coeff j H = 0

variable {p : ℕ}

theorem sparse_mul {t : ℕ} {G H : ℚ⟦X⟧} (hG : Sparse p t G) (hH : Sparse p t H) :
    Sparse p t (G * H) := by
  intro j hj
  rw [coeff_mul]
  apply sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : p ^ t ∣ x.1
  · have h2 : ¬ p ^ t ∣ x.2 := by
      intro h2
      apply hj
      rw [← hx]
      exact dvd_add h1 h2
    rw [hH _ h2, mul_zero]
  · rw [hG _ h1, zero_mul]

theorem sparse_pow {t : ℕ} {G : ℚ⟦X⟧} (hG : Sparse p t G) (n : ℕ) : Sparse p t (G ^ n) := by
  induction n with
  | zero =>
    intro j hj
    rw [pow_zero, coeff_one, if_neg]
    rintro rfl
    exact hj (dvd_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact sparse_mul ih hG

variable [hp : Fact p.Prime]

theorem sparse_expand {t : ℕ} {H : ℚ⟦X⟧} (hH : Sparse p t H) :
    Sparse p (t + 1) (expand p hp.out.ne_zero H) := by
  intro j hj
  rw [coeff_expand]
  split_ifs with hd
  · apply hH
    intro h
    apply hj
    obtain ⟨q, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left q hp.out.pos] at h
    rw [pow_succ']
    exact mul_dvd_mul_left p h
  · rfl

theorem pint_expand {H : ℚ⟦X⟧} (hH : PInt p H) : PInt p (expand p hp.out.ne_zero H) := by
  intro j
  rw [coeff_expand]
  split_ifs
  · exact hH _
  · exact V_zero_val _

theorem cong_refl (k : ℤ) (G : ℚ⟦X⟧) : Cong p k G G := by
  intro j
  rw [sub_self, map_zero]
  exact V_zero_val _

theorem cong_trans {k : ℤ} {G H K : ℚ⟦X⟧} (h1 : Cong p k G H) (h2 : Cong p k H K) :
    Cong p k G K := by
  intro j
  have := V_add (h1 j) (h2 j)
  rwa [← map_add, sub_add_sub_cancel] at this

theorem cong_mul {k : ℤ} {X₁ Y₁ X₂ Y₂ : ℚ⟦X⟧} (hX₂ : PInt p X₂) (hY₁ : PInt p Y₁)
    (h1 : Cong p k X₁ Y₁) (h2 : Cong p k X₂ Y₂) : Cong p k (X₁ * X₂) (Y₁ * Y₂) := by
  intro j
  have e : X₁ * X₂ - Y₁ * Y₂ = (X₁ - Y₁) * X₂ + Y₁ * (X₂ - Y₂) := by ring
  rw [e, map_add]
  have a1 := V_coeff_mul h1 hX₂ j
  have a2 := V_coeff_mul hY₁ h2 j
  rw [add_zero] at a1
  rw [zero_add] at a2
  exact V_add a1 a2

theorem cong_pow {k : ℤ} {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H) (h : Cong p k G H)
    (n : ℕ) : Cong p k (G ^ n) (H ^ n) := by
  induction n with
  | zero => exact cong_refl k 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cong_mul hG (pint_pow hH n) ih h

theorem cong_pow_p {k : ℤ} (hk : 1 ≤ k) {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H)
    (h : Cong p k G H) : Cong p (k + 1) (G ^ p) (H ^ p) := by
  set Q : ℚ⟦X⟧ := ∑ i ∈ range p, G ^ i * H ^ (p - 1 - i) with hQ
  have hfac : G ^ p - H ^ p = Q * (G - H) := (geom_sum₂_mul G H p).symm
  have e2 : ∑ i ∈ range p, H ^ i * H ^ (p - 1 - i) = ∑ i ∈ range p, H ^ (p - 1) := by
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [← pow_add, show i + (p - 1 - i) = p - 1 by omega]
  rw [sum_const, card_range] at e2
  have hsplit : Q = ∑ i ∈ range p, (G ^ i - H ^ i) * H ^ (p - 1 - i) + p • H ^ (p - 1) := by
    have e3 : Q = ∑ i ∈ range p, ((G ^ i - H ^ i) * H ^ (p - 1 - i)
        + H ^ i * H ^ (p - 1 - i)) := by
      rw [hQ]
      apply sum_congr rfl
      intro i _
      ring
    rw [sum_add_distrib, e2] at e3
    exact e3
  have hQV : ∀ j, V p 1 (coeff j Q) := by
    intro j
    rw [hsplit, map_add, map_sum]
    apply V_add
    · apply V_sum
      intro i _
      have := V_coeff_mul (cong_pow hG hH h i) (pint_pow hH (p - 1 - i)) j
      rw [add_zero] at this
      exact V_mono this hk
    · rw [map_nsmul, nsmul_eq_mul]
      have hpV : V p 1 (p : ℚ) := by simpa using V_p_pow (p := p) 1
      simpa using V_mul hpV (pint_pow hH (p - 1) j)
  intro j
  rw [hfac]
  have := V_coeff_mul hQV h j
  rwa [add_comm] at this

theorem cong_lift {G H : ℚ⟦X⟧} (hG : PInt p G) (hH : PInt p H) (h : Cong p 1 G H) (u : ℕ) :
    Cong p ((u : ℤ) + 1) (G ^ (p ^ u)) (H ^ (p ^ u)) := by
  induction u with
  | zero => simpa using h
  | succ u ih =>
    rw [pow_succ p u, pow_mul, pow_mul]
    have := cong_pow_p (by omega) (pint_pow hG _) (pint_pow hH _) ih
    push_cast
    exact this

theorem frob_full {G : ℚ⟦X⟧} (hG : PInt p G) :
    Cong p 1 (G ^ p) (expand p hp.out.ne_zero G) := by
  intro j
  have h := frob_trunc (p := p) (F := G) (j + 1) (fun i _ => hG i) j
  have e1 : coeff j (G ^ p) = coeff j ((truncS (j + 1) G) ^ p) :=
    coeff_pow_congr (k := j) (fun i hi => by rw [coeff_truncS, if_pos (by omega)]) p j le_rfl
  have e2 : coeff j (expand p hp.out.ne_zero G)
      = coeff j (expand p hp.out.ne_zero (truncS (j + 1) G)) := by
    rw [coeff_expand, coeff_expand]
    split_ifs with hd
    · rw [coeff_truncS, if_pos (by have := Nat.div_le_self j p; omega)]
    · rfl
  rw [map_sub, e1, e2, ← map_sub]
  exact h

theorem frob_iter {G : ℚ⟦X⟧} (hG : PInt p G) (t : ℕ) :
    ∃ H, PInt p H ∧ Sparse p t H ∧ Cong p 1 (G ^ (p ^ t)) H := by
  induction t with
  | zero =>
    refine ⟨G, hG, ?_, ?_⟩
    · intro j hj
      simp at hj
    · simpa using cong_refl (p := p) 1 G
  | succ t ih =>
    obtain ⟨H, hH, hS, hC⟩ := ih
    refine ⟨expand p hp.out.ne_zero H, pint_expand hH, sparse_expand hS, ?_⟩
    rw [pow_succ p t, pow_mul]
    exact cong_trans (cong_pow (pint_pow hG _) hH hC p) (frob_full hH)

/-- Lemma 6 (in the form used): if `p^{t+u} ∣ M` and `p^t ∤ s` then `v_p([x^s] G^M) ≥ u+1`. -/
theorem lemma6 {G : ℚ⟦X⟧} (hG : PInt p G) {t u M s : ℕ} (hM : p ^ (t + u) ∣ M)
    (hs : ¬ p ^ t ∣ s) : V p ((u : ℤ) + 1) (coeff s (G ^ M)) := by
  obtain ⟨H, hH, hS, hC⟩ := frob_iter hG t
  obtain ⟨m, rfl⟩ := hM
  have h1 := cong_lift (pint_pow hG (p ^ t)) hH hC u
  have h2 := cong_pow (pint_pow (pint_pow hG _) _) (pint_pow hH _) h1 m
  have hS2 : Sparse p t ((H ^ (p ^ u)) ^ m) := sparse_pow (sparse_pow hS _) m
  have e : G ^ (p ^ (t + u) * m) = ((G ^ (p ^ t)) ^ (p ^ u)) ^ m := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have h3 := h2 s
  rw [map_sub, hS2 s hs, sub_zero, ← e] at h3
  exact h3

end

end TF
