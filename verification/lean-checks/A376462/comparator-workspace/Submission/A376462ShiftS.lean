import Submission.A376462ShiftK

/-!
# A376462 shifted congruence, part 5: class S (§7)

Proof note: `proofs/A376462-shifted-congruence.md`, §7. `N = m p^(w+1)`, `M = m p^w`, `r = w+1`.
* `St_exact`: `S̃(N; pk′, pj′) = S̃(M; k′, j′) · E`, `E = P²_{pk′} P̄_{pk′} P²_{p(k′+j′)} P̄_{pj′}`.
* Step 1 (`S_step1`): termwise `S̃(N;pk′,pj′) - S̃(M;k′,j′) ≡ -N S̃(M;k′,j′) ρ_S (mod p^(3r))`
  via Lemma 1.3 (`E_so`) and the valuation bound `S1_val` (`exists_mu`, `choose_val`).
* Step 2 (`S_step2`): `S̃(M;k′,j′) (H′_{p(k′+j′)} - H′_{pk′} - H′_{pj′}) ≡ 0 (mod p^(2r))`.
  Deviation from the note: the bound `v(H′_{p(k′+j′)} - H′_{pk′} - H′_{pj′}) ≥ 2 + v(k′) + v(j′)`
  is obtained from Lemma 2.4 (second order, `H_shift2`) applied with the index of larger
  valuation as the shift, instead of the series for `Z`.
* Steps 3–4 (`strat`): `p^(2w+2d) ∣ Σ_{x < L_w} H′_{p^d x} C(L_w-1,x)^(2c) C(L_w+x-1,x) G_w(x)` for any
  tower `G`; this is the stratification of Steps 3–4 organised as an induction on the level
  (scaled `x` reduce by Lemma 1.1, unscaled `x` by Lemma 2.6 + Lemma 3.1).
  `T₁` uses `c = 1`, `G = G1`; `T₂` uses `c = 0`, `G = G2`.
-/

open Nat Finset

namespace A376462Shift

open ShiftLib

lemma dvd_mul2_sub {R : Type*} [CommRing R] {d a1 a2 b1 b2 : R}
    (h1 : d ∣ a1 - b1) (h2 : d ∣ a2 - b2) : d ∣ a1 * a2 - b1 * b2 := by
  have e : a1 * a2 - b1 * b2 = (a1 - b1) * a2 + b1 * (a2 - b2) := by ring
  rw [e]; exact dvd_add (h1.mul_right _) (h2.mul_left _)

lemma dvd_mul3_sub {R : Type*} [CommRing R] {d a1 a2 a3 b1 b2 b3 : R}
    (h1 : d ∣ a1 - b1) (h2 : d ∣ a2 - b2) (h3 : d ∣ a3 - b3) :
    d ∣ a1 * a2 * a3 - b1 * b2 * b3 :=
  dvd_mul2_sub (dvd_mul2_sub h1 h2) h3

section padic

variable (p : ℕ) [Fact p.Prime]

/-- §7: `S̃(N; pk′, pj′) = S̃(M; k′, j′) · E(k′, j′)` (Lemma 1.1, signs cancel). -/
theorem St_exact (m w k j : ℕ) (hm : 1 ≤ m) :
    ((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p])
      = ((St (m * p ^ w) k j : ℕ) : ℤ_[p])
        * (Pm p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k) ^ 2
          * Pp p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k)
          * Pm p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * (k + j)) ^ 2
          * Pp p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * j)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 := choose_pred_prod p m (w + 1) (p * k) hm (by omega)
  have h2 := choose_add_pred_prod p m (w + 1) (p * k) (by omega) (dvd_mul_right p k)
  have h3 := choose_pred_prod p m (w + 1) (p * (k + j)) hm (by omega)
  have h4 := choose_add_pred_prod p m (w + 1) (p * j) (by omega) (dvd_mul_right p j)
  rw [Nat.add_sub_cancel] at h1 h2 h3 h4
  rw [Nat.mul_div_cancel_left k hp0] at h1 h2
  rw [Nat.mul_div_cancel_left (k + j) hp0] at h3
  rw [Nat.mul_div_cancel_left j hp0] at h4
  have hsq : ∀ k : ℕ, ((-1 : ℤ_[p]) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set L := ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) with hL
  unfold St
  rw [show p * k + p * j = p * (k + j) by ring]
  push_cast
  rw [h1, h2, h3, h4]
  linear_combination
    ((((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) * Pm p L (p * k)) ^ 2
      * ((((m * p ^ w + k - 1).choose k : ℕ) : ℤ_[p]) * Pp p L (p * k))
      * ((((m * p ^ w + j - 1).choose j : ℕ) : ℤ_[p]) * Pp p L (p * j))
      * ((((m * p ^ w - 1).choose (k + j) : ℕ) : ℤ_[p]) * Pm p L (p * (k + j))) ^ 2
      * (((-1 : ℤ_[p]) ^ (p * (k + j) - (k + j))) ^ 2 * hsq (p * k - k)
        + hsq (p * (k + j) - (k + j)))

/-- Lemma 1.3 for `E = P²_{x₁} P̄_{x₁} P²_{x₂} P̄_{x₃}`:
`2(E - 1 + Lρ) ≡ L²(ρ² - Q) (mod L³)`, `ρ = H′_{x₁} + 2H′_{x₂} - H′_{x₃}`,
`Q = 3S₂(x₁) + 2S₂(x₂) + S₂(x₃)`. -/
theorem E_so (L : ℤ_[p]) (x1 x2 x3 : ℕ) :
    L ^ 3 ∣ 2 * (Pm p L x1 ^ 2 * Pp p L x1 * Pm p L x2 ^ 2 * Pp p L x3 - 1
        - L * -(H p x1 + 2 * H p x2 - H p x3))
      - L ^ 2 * ((H p x1 + 2 * H p x2 - H p x3) ^ 2
        - (3 * S p 2 x1 + 2 * S p 2 x2 + S p 2 x3)) := by
  have fa := fo_pow (Pm_fo p L x1) 2
  have fb := Pp_fo p L x1
  have fc := fo_pow (Pm_fo p L x2) 2
  have fd := Pp_fo p L x3
  have sa := so_pow (Pm_fo p L x1) (Pm_so p L x1) 2
  have sb := Pp_so p L x1
  have sc := so_pow (Pm_fo p L x2) (Pm_so p L x2) 2
  have sd := Pp_so p L x3
  obtain ⟨z, hz⟩ := so_mul (fo_mul (fo_mul fa fb) fc) fd
    (so_mul (fo_mul fa fb) fc (so_mul fa fb sa sb) sc) sd
  refine ⟨z, ?_⟩
  push_cast at hz
  linear_combination hz

/-- `p^(w - v_p(x)) ∣ C(m p^w + x - 1, x)` for `x ≥ 1`. -/
lemma choose_val (m w x : ℕ) (hx : 1 ≤ x) :
    (p : ℤ_[p]) ^ (w - x.factorization p) ∣ (((m * p ^ w + x - 1).choose x : ℕ) : ℤ_[p]) := by
  rcases le_or_gt w (x.factorization p) with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]; exact one_dvd _
  · apply A386548.padic_cancel p x (by omega) (w - x.factorization p)
    have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (choose_absorb_pred (m * p ^ w) x hx)
    push_cast at h
    rw [show w - x.factorization p + x.factorization p = w by omega, h]
    exact ⟨(m : ℤ_[p]) * (((m * p ^ w + x - 1).choose (x - 1) : ℕ) : ℤ_[p]), by ring⟩

lemma St_dvd_k (m w k j : ℕ) (hk : 1 ≤ k) :
    (p : ℤ_[p]) ^ (w - k.factorization p) ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) := by
  obtain ⟨u, hu⟩ := choose_val p m w k hk
  unfold St
  push_cast
  rw [hu]
  exact ⟨(((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) ^ 2 * u
    * (((m * p ^ w - 1).choose (k + j) : ℕ) : ℤ_[p]) ^ 2
    * (((m * p ^ w + j - 1).choose j : ℕ) : ℤ_[p]), by ring⟩

lemma St_dvd_j (m w k j : ℕ) (hj : 1 ≤ j) :
    (p : ℤ_[p]) ^ (w - j.factorization p) ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) := by
  obtain ⟨u, hu⟩ := choose_val p m w j hj
  unfold St
  push_cast
  rw [hu]
  exact ⟨(((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) ^ 2
    * (((m * p ^ w + k - 1).choose k : ℕ) : ℤ_[p])
    * (((m * p ^ w - 1).choose (k + j) : ℕ) : ℤ_[p]) ^ 2 * u, by ring⟩

lemma St_dvd_kj (m w k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (p : ℤ_[p]) ^ ((w - k.factorization p) + (w - j.factorization p))
      ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) := by
  obtain ⟨u, hu⟩ := choose_val p m w k hk
  obtain ⟨v, hv⟩ := choose_val p m w j hj
  unfold St
  push_cast
  rw [hu, hv, pow_add]
  exact ⟨(((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) ^ 2 * u
    * (((m * p ^ w - 1).choose (k + j) : ℕ) : ℤ_[p]) ^ 2 * v, by ring⟩

/-- The common valuation `μ` of Step 1. -/
lemma exists_mu (m w k j : ℕ) :
    ∃ μ, p ^ μ ∣ k ∧ p ^ μ ∣ j ∧ (p : ℤ_[p]) ^ (w - μ) ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) := by
  by_cases hk : k = 0
  · by_cases hj : j = 0
    · exact ⟨w, by simp [hk], by simp [hj], by simp⟩
    · exact ⟨j.factorization p, by simp [hk], Nat.ordProj_dvd j p,
        St_dvd_j p m w k j (by omega)⟩
  · by_cases hj : j = 0
    · exact ⟨k.factorization p, Nat.ordProj_dvd k p, by simp [hj],
        St_dvd_k p m w k j (by omega)⟩
    · rcases le_total (k.factorization p) (j.factorization p) with h | h
      · exact ⟨k.factorization p, Nat.ordProj_dvd k p,
          (pow_dvd_pow p h).trans (Nat.ordProj_dvd j p), St_dvd_k p m w k j (by omega)⟩
      · exact ⟨j.factorization p, (pow_dvd_pow p h).trans (Nat.ordProj_dvd k p),
          Nat.ordProj_dvd j p, St_dvd_j p m w k j (by omega)⟩

/-- Step 1 valuation bound: `p^r ∣ S̃(M;k′,j′) (ρ_S² - Q)`. -/
lemma S1_val (hp5 : 5 ≤ p) (m w k j : ℕ) :
    (p : ℤ_[p]) ^ (w + 1) ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p])
      * ((H p (p * k) + 2 * H p (p * (k + j)) - H p (p * j)) ^ 2
        - (3 * S p 2 (p * k) + 2 * S p 2 (p * (k + j)) + S p 2 (p * j))) := by
  obtain ⟨μ, hk, hj, hSt⟩ := exists_mu p m w k j
  have hd : ∀ x, p ^ μ ∣ x → p ^ (μ + 1) ∣ p * x := fun x hx => by
    rw [pow_succ']; exact mul_dvd_mul_left p hx
  have hk' := hd k hk
  have hj' := hd j hj
  have hkj' := hd (k + j) (dvd_add hk hj)
  have hH : ∀ x, p ^ (μ + 1) ∣ x → (p : ℤ_[p]) ^ (μ + 1) ∣ H p x := fun x hx =>
    (pow_dvd_pow _ (by omega)).trans (H_dvd p hp5 (μ + 1) x hx)
  have hS : ∀ x, p ^ (μ + 1) ∣ x → (p : ℤ_[p]) ^ (μ + 1) ∣ S p 2 x := fun x hx =>
    S2_dvd' p hp5 (μ + 1) x hx
  have hρ : (p : ℤ_[p]) ^ (μ + 1) ∣ H p (p * k) + 2 * H p (p * (k + j)) - H p (p * j) :=
    _root_.dvd_sub (dvd_add (hH _ hk') ((hH _ hkj').mul_left _)) (hH _ hj')
  have hQ : (p : ℤ_[p]) ^ (μ + 1)
      ∣ 3 * S p 2 (p * k) + 2 * S p 2 (p * (k + j)) + S p 2 (p * j) :=
    dvd_add (dvd_add ((hS _ hk').mul_left _) ((hS _ hkj').mul_left _)) (hS _ hj')
  have hb := _root_.dvd_sub (dvd_pow hρ two_ne_zero) hQ
  exact (pow_dvd_pow (p : ℤ_[p]) (show w + 1 ≤ (w - μ) + (μ + 1) by omega)).trans
    (by rw [pow_add]; exact mul_dvd_mul hSt hb)

/-- **Step 1** (termwise): `S̃(N;pk′,pj′) - S̃(M;k′,j′) + N S̃(M;k′,j′) ρ_S ≡ 0 (mod p^(3r))`. -/
lemma S_step1 (hp5 : 5 ≤ p) (m w k j : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p])
      - ((St (m * p ^ w) k j : ℕ) : ℤ_[p])
      + ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * (((St (m * p ^ w) k j : ℕ) : ℤ_[p])
        * (H p (p * k) + 2 * H p (p * (k + j)) - H p (p * j))) := by
  rw [St_exact p m w k j hm]
  obtain ⟨z, hz⟩ := E_so p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k) (p * (k + j)) (p * j)
  have h1 := S1_val p hp5 m w k j
  set L := ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) with hL
  set St0 := ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) with hSt0
  set ρ := H p (p * k) + 2 * H p (p * (k + j)) - H p (p * j) with hρ
  set Q := 3 * S p 2 (p * k) + 2 * S p 2 (p * (k + j)) + S p 2 (p * j) with hQ
  set E := Pm p L (p * k) ^ 2 * Pp p L (p * k) * Pm p L (p * (k + j)) ^ 2 * Pp p L (p * j) with hE
  have hL1 : (p : ℤ_[p]) ^ (w + 1) ∣ L := ppow_dvd_cast p m (w + 1)
  apply dvd_of_two_mul p hp5
  have e : 2 * (St0 * E - St0 + L * (St0 * ρ)) = L ^ 2 * (St0 * (ρ ^ 2 - Q)) + St0 * (L ^ 3 * z) := by
    linear_combination St0 * hz
  rw [e]
  apply dvd_add
  · rw [show 3 * (w + 1) = (w + 1) * 2 + (w + 1) by ring, pow_add, pow_mul]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hL1 2) h1
  · rw [show 3 * (w + 1) = (w + 1) * 3 by ring, pow_mul]
    exact ((pow_dvd_pow_of_dvd hL1 3).mul_right _).mul_left _

/-- `v(H′_{p(k′+j′)} - H′_{pk′} - H′_{pj′}) ≥ 2 + v(k′) + v(j′)` (Lemma 2.4, second order). -/
lemma D_val (hp5 : 5 ≤ p) (k j : ℕ) :
    (p : ℤ_[p]) ^ (2 + k.factorization p + j.factorization p)
      ∣ H p (p * (k + j)) - H p (p * k) - H p (p * j) := by
  have key : ∀ a b : ℕ, b.factorization p ≤ a.factorization p →
      (p : ℤ_[p]) ^ (2 + a.factorization p + b.factorization p)
        ∣ H p (p * a + p * b) - H p (p * a) - H p (p * b) := by
    intro a b hab
    have hc : p ^ (a.factorization p + 1) ∣ p * a := by
      rw [pow_succ']; exact mul_dvd_mul_left p (Nat.ordProj_dvd a p)
    have hx : p ^ (b.factorization p + 1) ∣ p * b := by
      rw [pow_succ']; exact mul_dvd_mul_left p (Nat.ordProj_dvd b p)
    have h1 := H_shift2 p (a.factorization p + 1) (p * a) (p * b) hc
    have h2 := S2_dvd' p hp5 (b.factorization p + 1) (p * b) hx
    have h3 : (p : ℤ_[p]) ^ (a.factorization p + 1) ∣ ((p * a : ℕ) : ℤ_[p]) := ppow_dvd_natCast p hc
    have h4 : (p : ℤ_[p]) ^ (2 + a.factorization p + b.factorization p)
        ∣ ((p * a : ℕ) : ℤ_[p]) * S p 2 (p * b) := by
      rw [show 2 + a.factorization p + b.factorization p
        = (a.factorization p + 1) + (b.factorization p + 1) by ring, pow_add]
      exact mul_dvd_mul h3 h2
    have h5 : (p : ℤ_[p]) ^ (2 + a.factorization p + b.factorization p)
        ∣ H p (p * a + p * b) - H p (p * a) - H p (p * b) + ((p * a : ℕ) : ℤ_[p]) * S p 2 (p * b) :=
      (pow_dvd_pow _ (by omega)).trans h1
    have := _root_.dvd_sub h5 h4
    rwa [add_sub_cancel_right] at this
  rcases le_total (j.factorization p) (k.factorization p) with h | h
  · rw [mul_add]; exact key k j h
  · have := key j k h
    rw [mul_add, add_comm (p * k) (p * j),
      show 2 + k.factorization p + j.factorization p = 2 + j.factorization p + k.factorization p
        by ring,
      show H p (p * j + p * k) - H p (p * k) - H p (p * j)
        = H p (p * j + p * k) - H p (p * j) - H p (p * k) by ring]
    exact this

/-- **Step 2** (termwise). -/
lemma S_step2 (hp5 : 5 ≤ p) (m w k j : ℕ) :
    (p : ℤ_[p]) ^ (2 * (w + 1)) ∣ ((St (m * p ^ w) k j : ℕ) : ℤ_[p])
      * (H p (p * (k + j)) - H p (p * k) - H p (p * j)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [H_zero]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp [H_zero]
  have hSt := St_dvd_kj p m w k j hk hj
  have hD := D_val p hp5 k j
  exact (pow_dvd_pow (p : ℤ_[p]) (show 2 * (w + 1) ≤ (w - k.factorization p
    + (w - j.factorization p)) + (2 + k.factorization p + j.factorization p) by omega)).trans
    (by rw [pow_add]; exact mul_dvd_mul hSt hD)

/- ### Steps 3–4: the stratified sums -/

/-- The kernel of the stratified induction at level `u` (`R̂^{(u)}` of Step 3, `c = 1`). -/
noncomputable def Wt (m c : ℕ) (G : ℕ → ℕ → ℤ_[p]) (u q : ℕ) : ℤ_[p] :=
  (((m * p ^ u - 1).choose q : ℕ) : ℤ_[p]) ^ (2 * c) * (((m * p ^ u + q).choose q : ℕ) : ℤ_[p])
    * G u q

lemma neg_one_pow_pow (k c : ℕ) : ((-1 : ℤ_[p]) ^ k) ^ (2 * c) = 1 := by
  rw [← pow_mul, show k * (2 * c) = 2 * (k * c) by ring, pow_mul, neg_one_sq, one_pow]

lemma cong_pow_pred (m s n c : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ (((m * p ^ s - 1).choose n : ℕ) : ℤ_[p]) ^ (2 * c)
      - (((m * p ^ (s - 1) - 1).choose (n / p) : ℕ) : ℤ_[p]) ^ (2 * c) := by
  have h := (cong_pred p m s n hm hs).trans (sub_dvd_pow_sub_pow _ _ (2 * c))
  rwa [mul_pow, mul_pow, neg_one_pow_pow, neg_one_pow_pow, one_mul, one_mul] at h

lemma Wt_tower (m c : ℕ) (hm : 1 ≤ m) (G : ℕ → ℕ → ℤ_[p])
    (hG : ∀ w x, (p : ℤ_[p]) ^ (w + 1) ∣ G (w + 1) x - G w (x / p)) (u : ℕ) (hu : 1 ≤ u) (k : ℕ) :
    (p : ℤ_[p]) ^ u ∣ Wt p m c G u k - Wt p m c G (u - 1) (k / p) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  unfold Wt
  have h1 := cong_pow_pred p m (v + 1) k c hm (by omega)
  have h2 := cong_add p m (v + 1) k (by omega)
  rw [Nat.add_sub_cancel] at h1 h2 ⊢
  exact dvd_mul3_sub h1 h2 (hG v k)

/-- Scaled terms of the stratified induction. -/
lemma strat_term (hp5 : 5 ≤ p) (m c : ℕ) (hm : 1 ≤ m) (G : ℕ → ℕ → ℤ_[p])
    (hG : ∀ w x, (p : ℤ_[p]) ^ (w + 1) ∣ G (w + 1) x - G w (x / p)) (w d y : ℕ) :
    (p : ℤ_[p]) ^ (2 * (w + 1) + 2 * d) ∣
      H p (p ^ d * (p * y)) * ((((m * p ^ (w + 1) - 1).choose (p * y) : ℕ) : ℤ_[p]) ^ (2 * c)
        * (((m * p ^ (w + 1) + p * y - 1).choose (p * y) : ℕ) : ℤ_[p]) * G (w + 1) (p * y))
      - H p (p ^ (d + 1) * y) * ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c)
        * (((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]) * G w y) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [show p ^ d * (p * y) = p ^ (d + 1) * y by ring]
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp [H_zero]
  have h1 := choose_pred_prod p m (w + 1) (p * y) hm (by omega)
  have h2 := choose_add_pred_prod p m (w + 1) (p * y) (by omega) (dvd_mul_right p y)
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left y hp0] at h1 h2
  rw [h1, h2]
  have hGy := hG w (p * y)
  rw [Nat.mul_div_cancel_left y hp0] at hGy
  have hH := H_dvd p hp5 (d + 1 + y.factorization p) (p ^ (d + 1) * y)
    (by rw [pow_add]; exact mul_dvd_mul_left _ (Nat.ordProj_dvd y p))
  have hC2 := choose_val p m w y hy
  set L := ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) with hL
  have hPm := Pm_sub_one_dvd p L (w + 1) (p * y) (ppow_dvd_cast p m (w + 1))
  have hPp := Pp_sub_one_dvd p L (w + 1) (p * y) (ppow_dvd_cast p m (w + 1))
  have hP : (p : ℤ_[p]) ^ (w + 1) ∣ Pm p L (p * y) ^ (2 * c) * Pp p L (p * y) - 1 := by
    have e : Pm p L (p * y) ^ (2 * c) * Pp p L (p * y) - 1
        = (Pm p L (p * y) ^ (2 * c) - 1) * Pp p L (p * y) + (Pp p L (p * y) - 1) := by ring
    rw [e]
    exact dvd_add ((hPm.trans (sub_one_dvd_pow_sub_one _ _)).mul_right _) hPp
  have e : H p (p ^ (d + 1) * y)
        * (((-1 : ℤ_[p]) ^ (p * y - y) * (((m * p ^ w - 1).choose y : ℕ) : ℤ_[p])
            * Pm p L (p * y)) ^ (2 * c)
          * ((((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]) * Pp p L (p * y)) * G (w + 1) (p * y))
      - H p (p ^ (d + 1) * y) * ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c)
        * (((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]) * G w y)
      = (H p (p ^ (d + 1) * y) * (((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]))
        * ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c)
          * ((Pm p L (p * y) ^ (2 * c) * Pp p L (p * y) - 1) * G (w + 1) (p * y)
            + (G (w + 1) (p * y) - G w y))) := by
    rw [mul_pow, mul_pow, neg_one_pow_pow]
    ring
  rw [e]
  have hbr := (dvd_add (hP.mul_right (G (w + 1) (p * y))) hGy).mul_left
    ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c))
  have := mul_dvd_mul (mul_dvd_mul hH hC2) hbr
  rw [← pow_add, ← pow_add] at this
  exact (pow_dvd_pow _ (by omega)).trans this

/-- **Steps 3–4** (stratified induction): for a tower `G`,
`p^(2w+2d) ∣ Σ_{x < L_w} H′_{p^d x} C(L_w-1,x)^(2c) C(L_w+x-1,x) G_w(x)`. -/
theorem strat (hp5 : 5 ≤ p) (m c : ℕ) (hm : 1 ≤ m) (G : ℕ → ℕ → ℤ_[p])
    (hG : ∀ w x, (p : ℤ_[p]) ^ (w + 1) ∣ G (w + 1) x - G w (x / p)) (w d : ℕ) :
    (p : ℤ_[p]) ^ (2 * w + 2 * d) ∣ ∑ x ∈ range (m * p ^ w), H p (p ^ d * x)
      * ((((m * p ^ w - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
        * (((m * p ^ w + x - 1).choose x : ℕ) : ℤ_[p]) * G w x) := by
  induction w generalizing d with
  | zero =>
    apply Finset.dvd_sum; intro x _
    rw [mul_zero, zero_add]
    exact (H_dvd p hp5 d (p ^ d * x) (dvd_mul_right _ _)).mul_right _
  | succ w ih =>
    have hsplit := sum_range_mul_split p (m * p ^ w) (fun x => H p (p ^ d * x)
      * ((((m * p ^ (w + 1) - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
        * (((m * p ^ (w + 1) + x - 1).choose x : ℕ) : ℤ_[p]) * G (w + 1) x))
    rw [show p * (m * p ^ w) = m * p ^ (w + 1) by ring] at hsplit
    rw [hsplit]
    apply dvd_add
    · -- scaled indices
      have e : ∑ y ∈ range (m * p ^ w), H p (p ^ d * (p * y))
            * ((((m * p ^ (w + 1) - 1).choose (p * y) : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ (w + 1) + p * y - 1).choose (p * y) : ℕ) : ℤ_[p]) * G (w + 1) (p * y))
          = ∑ y ∈ range (m * p ^ w), (H p (p ^ d * (p * y))
            * ((((m * p ^ (w + 1) - 1).choose (p * y) : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ (w + 1) + p * y - 1).choose (p * y) : ℕ) : ℤ_[p]) * G (w + 1) (p * y))
            - H p (p ^ (d + 1) * y) * ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]) * G w y))
          + ∑ y ∈ range (m * p ^ w), H p (p ^ (d + 1) * y)
            * ((((m * p ^ w - 1).choose y : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ w + y - 1).choose y : ℕ) : ℤ_[p]) * G w y) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro y _; ring
      rw [e]
      apply dvd_add
      · exact Finset.dvd_sum fun y _ => strat_term p hp5 m c hm G hG w d y
      · rw [show 2 * (w + 1) + 2 * d = 2 * w + 2 * (d + 1) by ring]
        exact ih (d + 1)
    · -- unscaled indices
      have hfilt : ∑ x ∈ (range (m * p ^ (w + 1))).filter (fun x => ¬ p ∣ x), H p (p ^ d * x)
            * ((((m * p ^ (w + 1) - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ (w + 1) + x - 1).choose x : ℕ) : ℤ_[p]) * G (w + 1) x)
          = ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * ∑ x ∈ range (m * p ^ (w + 1)),
              Ring.inverse (x : ℤ_[p]) * H p (x * p ^ d)
                * ((((m * p ^ (w + 1) - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
                  * (((m * p ^ (w + 1) + x - 1).choose (x - 1) : ℕ) : ℤ_[p]) * G (w + 1) x) := by
        rw [Finset.mul_sum, ← sum_filter_ndvd p (range (m * p ^ (w + 1))) _
          (fun x hx => by rw [inv_eq_zero_of_dvd p hx]; ring)]
        apply Finset.sum_congr rfl
        intro x hx
        rw [choose_unsc_eq p (m * p ^ (w + 1)) x (Finset.mem_filter.mp hx).2, mul_comm (p ^ d) x]
        ring
      rw [hfilt]
      have hT : ∀ u, 1 ≤ u → u < w + 1 → ∀ k,
          (p : ℤ_[p]) ^ u ∣ Wt p m c G u k - Wt p m c G (u - 1) (k / p) :=
        fun u hu _ k => Wt_tower p m c hm G hG u hu k
      have hF : ∀ k : ℕ, (fun x : ℕ => Ring.inverse (x : ℤ_[p]) * H p (x * p ^ d)) k = 0 ∨
          (p : ℤ_[p]) ^ (w + 1) ∣ (fun x : ℕ => (((m * p ^ (w + 1) - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
              * (((m * p ^ (w + 1) + x - 1).choose (x - 1) : ℕ) : ℤ_[p]) * G (w + 1) x) k
            - Wt p m c G (w + 1 - 1) (k / p) := by
        intro k
        by_cases hk : p ∣ k
        · left; simp [inv_eq_zero_of_dvd p hk]
        · right
          unfold Wt
          have h1 := cong_pow_pred p m (w + 1) k c hm (by omega)
          have h2 := cong_add_pred_pred p m (w + 1) k (by omega) hk
          rw [Nat.add_sub_cancel] at h1 h2 ⊢
          exact dvd_mul3_sub h1 h2 (hG w k)
      have hb := block_ind_top_range p (Wt p m c G) (w + 1) (2 * d) hT
        (fun x : ℕ => (((m * p ^ (w + 1) - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * c)
          * (((m * p ^ (w + 1) + x - 1).choose (x - 1) : ℕ) : ℤ_[p]) * G (w + 1) x)
        (fun x : ℕ => Ring.inverse (x : ℤ_[p]) * H p (x * p ^ d)) hF
        (fun t _ l => dh2 p hp5 d t l) m
      rw [show 2 * (w + 1) + 2 * d = (w + 1) + (w + 1 + 2 * d) by ring, pow_add]
      exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) hb

/-- `G₁^{(w)}(x) = Σ_{j < L_w} C(L_w-1, x+j)² C(L_w+j-1, j)` (Step 3). -/
noncomputable def G1 (m w x : ℕ) : ℤ_[p] :=
  ∑ j ∈ range (m * p ^ w), (((m * p ^ w - 1).choose (x + j) : ℕ) : ℤ_[p]) ^ 2
    * (((m * p ^ w + j - 1).choose j : ℕ) : ℤ_[p])

/-- `G₂^{(w)}(y) = Σ_{k < L_w} C(L_w-1,k)² C(L_w+k-1,k) C(L_w-1,k+y)²` (Step 4). -/
noncomputable def G2 (m w y : ℕ) : ℤ_[p] :=
  ∑ k ∈ range (m * p ^ w), (((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) ^ 2
    * (((m * p ^ w + k - 1).choose k : ℕ) : ℤ_[p]) * (((m * p ^ w - 1).choose (k + y) : ℕ) : ℤ_[p]) ^ 2

lemma G1_tower (m : ℕ) (hm : 1 ≤ m) (w x : ℕ) :
    (p : ℤ_[p]) ^ (w + 1) ∣ G1 p m (w + 1) x - G1 p m w (x / p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold G1
  rw [show range (m * p ^ (w + 1)) = range (p * (m * p ^ w)) by
    rw [show m * p ^ (w + 1) = p * (m * p ^ w) by ring]]
  refine split_tower p (m * p ^ w) (w + 1) _ _ (fun j => ?_) (fun j hj => ?_)
  · have h1 := cong_sq_pred p m (w + 1) (x + p * j) hm (by omega)
    rw [Nat.add_sub_cancel, Nat.add_mul_div_left x j hp0] at h1
    have h2 := cong_add_pred p m (w + 1) j (by omega)
    rw [Nat.add_sub_cancel] at h2
    exact dvd_mul2_sub h1 h2
  · exact (choose_unsc p m (w + 1) j hj).mul_left _

lemma G2_tower (m : ℕ) (hm : 1 ≤ m) (w y : ℕ) :
    (p : ℤ_[p]) ^ (w + 1) ∣ G2 p m (w + 1) y - G2 p m w (y / p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold G2
  rw [show range (m * p ^ (w + 1)) = range (p * (m * p ^ w)) by
    rw [show m * p ^ (w + 1) = p * (m * p ^ w) by ring]]
  refine split_tower p (m * p ^ w) (w + 1) _ _ (fun k => ?_) (fun k hk => ?_)
  · have h1 := cong_sq_pred p m (w + 1) (p * k) hm (by omega)
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left k hp0] at h1
    have h2 := cong_add_pred p m (w + 1) k (by omega)
    rw [Nat.add_sub_cancel] at h2
    have h3 := cong_sq_pred p m (w + 1) (p * k + y) hm (by omega)
    rw [Nat.add_sub_cancel, Nat.mul_add_div hp0 k y] at h3
    exact dvd_mul3_sub h1 h2 h3
  · exact ((choose_unsc p m (w + 1) k hk).mul_left _).mul_right _

/-- **Class S** (§7): `Σ_S - a(M-1) ≡ 0 (mod p^(3r))`. -/
theorem classS (hp5 : 5 ≤ p) (m w : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      (((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p]) - ((St (m * p ^ w) k j : ℕ) : ℤ_[p])) := by
  -- Step 3: T₁
  have hT1 : (p : ℤ_[p]) ^ (2 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * k) := by
    have h := strat p hp5 m 1 hm (G1 p m) (G1_tower p m hm) w 1
    have e : ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
          ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * k)
        = ∑ x ∈ range (m * p ^ w), H p (p ^ 1 * x)
          * ((((m * p ^ w - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * 1)
            * (((m * p ^ w + x - 1).choose x : ℕ) : ℤ_[p]) * G1 p m w x) := by
      apply Finset.sum_congr rfl; intro k _
      unfold G1
      rw [pow_one, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      unfold St
      push_cast
      ring
    rw [e, show 2 * (w + 1) = 2 * w + 2 * 1 by ring]
    exact h
  -- Step 4: T₂
  have hT2 : (p : ℤ_[p]) ^ (2 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * j) := by
    have h := strat p hp5 m 0 hm (G2 p m) (G2_tower p m hm) w 1
    have e : ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
          ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * j)
        = ∑ x ∈ range (m * p ^ w), H p (p ^ 1 * x)
          * ((((m * p ^ w - 1).choose x : ℕ) : ℤ_[p]) ^ (2 * 0)
            * (((m * p ^ w + x - 1).choose x : ℕ) : ℤ_[p]) * G2 p m w x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      unfold G2
      rw [pow_one, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      unfold St
      push_cast
      ring
    rw [e, show 2 * (w + 1) = 2 * w + 2 * 1 by ring]
    exact h
  -- Step 2 summed
  have hTD : (p : ℤ_[p]) ^ (2 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * (H p (p * (k + j)) - H p (p * k) - H p (p * j)) :=
    Finset.dvd_sum fun k _ => Finset.dvd_sum fun j _ => S_step2 p hp5 m w k j
  have hB : (p : ℤ_[p]) ^ (2 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      (3 * (((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * k))
        + ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * j)
        + 2 * (((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * (H p (p * (k + j)) - H p (p * k) - H p (p * j)))) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact dvd_add (dvd_add (hT1.mul_left 3) hT2) (hTD.mul_left 2)
  -- assemble (Step 1 termwise)
  have e : ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
      (((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p]) - ((St (m * p ^ w) k j : ℕ) : ℤ_[p]))
      = ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
          (((St (m * p ^ (w + 1)) (p * k) (p * j) : ℕ) : ℤ_[p]) - ((St (m * p ^ w) k j : ℕ) : ℤ_[p])
            + ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * (((St (m * p ^ w) k j : ℕ) : ℤ_[p])
              * (H p (p * k) + 2 * H p (p * (k + j)) - H p (p * j))))
        - ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * ∑ k ∈ range (m * p ^ w), ∑ j ∈ range (m * p ^ w),
          (3 * (((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * k))
            + ((St (m * p ^ w) k j : ℕ) : ℤ_[p]) * H p (p * j)
            + 2 * (((St (m * p ^ w) k j : ℕ) : ℤ_[p])
              * (H p (p * (k + j)) - H p (p * k) - H p (p * j)))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [e]
  refine _root_.dvd_sub (Finset.dvd_sum fun k _ => Finset.dvd_sum fun j _ =>
    S_step1 p hp5 m w k j hm) ?_
  rw [show 3 * (w + 1) = (w + 1) + 2 * (w + 1) by ring, pow_add]
  exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) hB

end padic

end A376462Shift
