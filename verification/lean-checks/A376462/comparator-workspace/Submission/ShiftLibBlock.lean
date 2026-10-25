import Submission.ShiftLibHarm

/-!
# A376462 shifted congruence, lemma bank §3: block inductions, kernels, towers

Proof note: `proofs/A376462-shifted-congruence.md`, §3 (Lemmas 3.1–3.5).

* Lemma 3.1 (`block_ind`, `block_ind_top` and `_range` forms) and Lemma 3.2 (`block_ind2`,
  `block_ind2_top`, `_range`) are stated with an extra *scale* `e`: the block (cell) sums of the
  weights at level `t` are assumed `≡ 0 (mod p^(t+e))` for all `0 ≤ t ≤ s`, and the conclusion is
  `≡ 0 (mod p^(s+e))`. With `e = 0` this is the note's statement (the level-0 condition is then
  empty); `e > 0` is the note's use with the integral weights `a/p^e`, without dividing.
* Kernels, for `L = L_u = m p^u ≥ 1` (all `ℕ`-valued; negative binomials rewritten as in §1):
  `Psi L n j = Ψ_u(n,j) = C(L-1,n)² C(L+n,n) C(L-1,n+j)² C(L+j-1,j)`,
  `Kk L n = K_u(n) = Σ_{j<L} Ψ_u(n,j)`,
  `Xi L δ q q' = Ξ_u^{(δ)}(q,q') = C(L-1,q)² C(L+q,q) C(L-1,q+q'+δ)² C(L+q',q')`,
  `Xih L n j = Ξ̂_u(n,j) = C(L-1,n)² C(L+n,n) C(L-1,n+j)² C(L+j-1,j-1)` (meaningful for `j ≥ 1`),
  `St N k j = S̃(N;k,j) = C(N-1,k)² C(N+k-1,k) C(N-1,k+j)² C(N+j-1,j)`,
  `Kw p L n g = Σ_{j<L} Ψ_u(n,j) g(j)` (weighted kernels: `g = 1`, `g = j^t`, `g = H′_{p^d j}`).
-/

open Nat Finset

namespace ShiftLib

section block

variable (p : ℕ) [Fact p.Prime]

/- ### Lemma 3.1 (one-index block induction) -/

omit [Fact p.Prime] in
lemma div_of_mem_blk_one {q k : ℕ} (hk : k ∈ blk p 1 q) : k / p = q := by
  unfold blk at hk
  rw [Finset.mem_Ico, pow_one] at hk
  exact Nat.div_eq_of_lt_le hk.1 hk.2

/-- **Lemma 3.1** (scaled form). -/
theorem block_ind (T : ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u ≤ s → ∀ k, (p : ℤ_[p]) ^ u ∣ T u k - T (u - 1) (k / p))
    (a : ℕ → ℤ_[p]) (ha : ∀ t, t ≤ s → ∀ l, (p : ℤ_[p]) ^ (t + e) ∣ ∑ k ∈ blk p t l, a k)
    (l : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣ ∑ k ∈ blk p s l, a k * T s k := by
  have key : ∀ s', s' ≤ s → ∀ (e : ℕ) (a : ℕ → ℤ_[p]),
      (∀ t, t ≤ s' → ∀ l, (p : ℤ_[p]) ^ (t + e) ∣ ∑ k ∈ blk p t l, a k) →
      ∀ l, (p : ℤ_[p]) ^ (s' + e) ∣ ∑ k ∈ blk p s' l, a k * T s' k := by
    intro s'
    induction s' with
    | zero =>
      intro _ e a ha l
      have h := ha 0 le_rfl l
      rw [blk_zero, Finset.sum_singleton] at h ⊢
      exact h.mul_right _
    | succ s ih =>
    intro hss e a ha l
    have ha0 : ∀ k, (p : ℤ_[p]) ^ e ∣ a k := by
      intro k
      have h := ha 0 (by omega) k
      rwa [blk_zero, Finset.sum_singleton, zero_add] at h
    have hm := blk_merge p 1 s l (fun k => a k * T (s + 1) k)
    rw [show 1 + s = s + 1 by ring] at hm
    rw [← hm]
    have e1 : ∀ q ∈ blk p s l, ∑ k ∈ blk p 1 q, a k * T (s + 1) k
        = ∑ k ∈ blk p 1 q, a k * (T (s + 1) k - T s q) + (∑ k ∈ blk p 1 q, a k) * T s q := by
      intro q _
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    apply dvd_add
    · apply Finset.dvd_sum; intro q _
      apply Finset.dvd_sum; intro k hk
      have h1 := hT (s + 1) (by omega) hss k
      rw [Nat.add_sub_cancel, div_of_mem_blk_one p hk] at h1
      rw [show s + 1 + e = e + (s + 1) by ring, pow_add]
      exact mul_dvd_mul (ha0 k) h1
    · have ha' : ∀ t, t ≤ s → ∀ l, (p : ℤ_[p]) ^ (t + (e + 1)) ∣
          ∑ q ∈ blk p t l, ∑ k ∈ blk p 1 q, a k := by
        intro t ht l'
        rw [blk_merge p 1 t l', show t + (e + 1) = (1 + t) + e by ring]
        exact ha (1 + t) (by omega) l'
      have h := ih (by omega) (e + 1) (fun q => ∑ k ∈ blk p 1 q, a k) ha' l
      rwa [show s + (e + 1) = s + 1 + e by ring] at h
  exact key s le_rfl e a ha l

/-- Lemma 3.1 over `k < M p^s` (`M` full blocks). -/
theorem block_ind_range (T : ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u ≤ s → ∀ k, (p : ℤ_[p]) ^ u ∣ T u k - T (u - 1) (k / p))
    (a : ℕ → ℤ_[p]) (ha : ∀ t, t ≤ s → ∀ l, (p : ℤ_[p]) ^ (t + e) ∣ ∑ k ∈ blk p t l, a k)
    (M : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣ ∑ k ∈ range (M * p ^ s), a k * T s k := by
  rw [sum_range_blk]
  exact Finset.dvd_sum (fun l _ => block_ind p T s e hT a ha l)

/-- Lemma 3.1 with a separate top-level function `F` (Beukers' Lemma 3(ii)): the tower
congruence `F k ≡ T_{s-1}([k/p]) (mod p^s)` is only needed where the weight is nonzero. -/
theorem block_ind_top (T : ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u < s → ∀ k, (p : ℤ_[p]) ^ u ∣ T u k - T (u - 1) (k / p))
    (F : ℕ → ℤ_[p]) (a : ℕ → ℤ_[p])
    (hF : ∀ k, a k = 0 ∨ (p : ℤ_[p]) ^ s ∣ F k - T (s - 1) (k / p))
    (ha : ∀ t, t ≤ s → ∀ l, (p : ℤ_[p]) ^ (t + e) ∣ ∑ k ∈ blk p t l, a k) (l : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣ ∑ k ∈ blk p s l, a k * F k := by
  set T' : ℕ → ℕ → ℤ_[p] := fun u k => if u < s then T u k else T (s - 1) (k / p) with hT'
  have hT'tower : ∀ u, 1 ≤ u → u ≤ s → ∀ k, (p : ℤ_[p]) ^ u ∣ T' u k - T' (u - 1) (k / p) := by
    intro u hu1 hu k
    rcases Nat.lt_or_ge u s with hlt | hge
    · simp only [hT', if_pos hlt, if_pos (show u - 1 < s by omega)]
      exact hT u hu1 hlt k
    · have hus : u = s := le_antisymm hu hge
      subst hus
      simp only [hT', lt_irrefl, if_false, if_pos (show u - 1 < u by omega), sub_self]
      exact dvd_zero _
  have ha0 : ∀ k, (p : ℤ_[p]) ^ e ∣ a k := by
    intro k
    have h := ha 0 (by omega) k
    rwa [blk_zero, Finset.sum_singleton, zero_add] at h
  have e1 : ∑ k ∈ blk p s l, a k * F k
      = ∑ k ∈ blk p s l, a k * (F k - T' s k) + ∑ k ∈ blk p s l, a k * T' s k := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  rw [e1]
  refine dvd_add (Finset.dvd_sum fun k _ => ?_) (block_ind p T' s e hT'tower a ha l)
  rcases hF k with h0 | hk
  · rw [h0, zero_mul]; exact dvd_zero _
  · have hTs : T' s k = T (s - 1) (k / p) := by simp only [hT', lt_irrefl, if_false]
    rw [hTs, add_comm, pow_add]
    exact mul_dvd_mul (ha0 k) hk

theorem block_ind_top_range (T : ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u < s → ∀ k, (p : ℤ_[p]) ^ u ∣ T u k - T (u - 1) (k / p))
    (F : ℕ → ℤ_[p]) (a : ℕ → ℤ_[p])
    (hF : ∀ k, a k = 0 ∨ (p : ℤ_[p]) ^ s ∣ F k - T (s - 1) (k / p))
    (ha : ∀ t, t ≤ s → ∀ l, (p : ℤ_[p]) ^ (t + e) ∣ ∑ k ∈ blk p t l, a k) (M : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣ ∑ k ∈ range (M * p ^ s), a k * F k := by
  rw [sum_range_blk]
  exact Finset.dvd_sum (fun l _ => block_ind_top p T s e hT F a hF ha l)

/- ### Lemma 3.2 (two-index block induction with carries) -/

/-- Cell sum at level `t`: `Σ_{(q,q',δ) ∈ Cell_t(i,i';c)} a^{(δ)}_{q,q'}`, `δ ∈ {0,1}`. -/
noncomputable def cellSum (a : ℕ → ℕ → ℕ → ℤ_[p]) (t i i' c : ℕ) : ℤ_[p] :=
  ∑ q ∈ blk p t i, ∑ q' ∈ blk p t i', ∑ δ ∈ range 2, if cry p t q q' δ = c then a δ q q' else 0

omit [Fact p.Prime] in
/-- Carries compose: `[(q+q'+δ)/p] = [q/p] + [q'/p] + δ'` with `δ' = cry p 1 q q' δ`. -/
lemma add_div_cry (hp : 0 < p) (q q' δ : ℕ) (hδ : δ < 2) :
    (q + q' + δ) / p = q / p + q' / p + cry p 1 q q' δ := by
  have hq := Nat.div_add_mod q p
  have hq' := Nat.div_add_mod q' p
  have hr := Nat.mod_lt q hp
  have hr' := Nat.mod_lt q' hp
  unfold cry
  rw [pow_one]
  have e : q + q' + δ = (q % p + q' % p + δ) + p * (q / p + q' / p) := by linarith
  rw [e, Nat.add_mul_div_left _ _ hp]
  split_ifs with h
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; ring
  · rw [Nat.div_eq_of_lt (by omega)]; ring

omit [Fact p.Prime] in
/-- Carries compose across levels. -/
lemma cry_succ (hp : 0 < p) (t q q' δ : ℕ) (hδ : δ < 2) :
    cry p (t + 1) q q' δ = cry p t (q / p) (q' / p) (cry p 1 q q' δ) := by
  have hpt : 0 < p ^ t := pow_pos hp t
  have hm : ∀ x, x % p ^ (t + 1) = p * ((x / p) % p ^ t) + x % p := by
    intro x
    rw [pow_succ, mul_comm (p ^ t) p, Nat.mod_mul]
    ring
  have hr := Nat.mod_lt q hp
  have hr' := Nat.mod_lt q' hp
  have hx := Nat.mod_lt (q / p) hpt
  have hx' := Nat.mod_lt (q' / p) hpt
  unfold cry
  rw [hm q, hm q', pow_one, pow_succ, mul_comm (p ^ t) p]
  set X := (q / p) % p ^ t
  set X' := (q' / p) % p ^ t
  set r := q % p
  set r' := q' % p
  set P := p ^ t
  by_cases hc : p ≤ r + r' + δ
  · rw [if_pos hc]
    have e : p * X + r + (p * X' + r') + δ = p * (X + X' + 1) + (r + r' + δ - p) := by
      have := Nat.sub_add_cancel hc
      rw [Nat.mul_add, Nat.mul_add, mul_one]; omega
    rw [e]
    by_cases h2 : P ≤ X + X' + 1
    · rw [if_pos h2, if_pos]
      calc p * P ≤ p * (X + X' + 1) := Nat.mul_le_mul_left _ h2
        _ ≤ _ := Nat.le_add_right _ _
    · rw [if_neg h2, if_neg]
      have h3 : X + X' + 1 + 1 ≤ P := by omega
      have h4 : p * (X + X' + 1 + 1) ≤ p * P := Nat.mul_le_mul_left _ h3
      rw [Nat.mul_add, mul_one] at h4
      omega
  · rw [if_neg hc]
    have e : p * X + r + (p * X' + r') + δ = p * (X + X' + 0) + (r + r' + δ) := by ring
    rw [e]
    by_cases h2 : P ≤ X + X' + 0
    · rw [if_pos h2, if_pos]
      calc p * P ≤ p * (X + X' + 0) := Nat.mul_le_mul_left _ h2
        _ ≤ _ := Nat.le_add_right _ _
    · rw [if_neg h2, if_neg]
      have h3 : X + X' + 0 + 1 ≤ P := by omega
      have h4 : p * (X + X' + 0 + 1) ≤ p * P := Nat.mul_le_mul_left _ h3
      rw [Nat.mul_add, mul_one] at h4
      omega

omit [Fact p.Prime] in
lemma cry_zero (l l' δ : ℕ) (hδ : δ < 2) : cry p 0 l l' δ = δ := by
  unfold cry
  interval_cases δ <;> simp [Nat.mod_one]

lemma cell_zero (a : ℕ → ℕ → ℕ → ℤ_[p]) (l l' c : ℕ) (hc : c < 2) :
    cellSum p a 0 l l' c = a c l l' := by
  unfold cellSum
  rw [blk_zero, blk_zero, Finset.sum_singleton, Finset.sum_singleton]
  have h : ∀ δ ∈ range 2, (if cry p 0 l l' δ = c then a δ l l' else 0)
      = (if δ = c then a δ l l' else 0) := by
    intro δ hδ; rw [cry_zero p l l' δ (Finset.mem_range.mp hδ)]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hc)]

omit [Fact p.Prime] in
lemma sum_comm3 {M : Type*} [AddCommMonoid M] {α β γ δ : Type*} (sa : Finset α) (sb : Finset β)
    (sc : Finset γ) (sd : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ d ∈ sd, f a b c d
      = ∑ d ∈ sd, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, f a b c d := by
  calc ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ d ∈ sd, f a b c d
      = ∑ a ∈ sa, ∑ b ∈ sb, ∑ d ∈ sd, ∑ c ∈ sc, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ sa, ∑ d ∈ sd, ∑ b ∈ sb, ∑ c ∈ sc, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d ∈ sd, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, f a b c d := Finset.sum_comm

/-- Regrouping one level: `Σ_{B_{s+1}×B_{s+1}×δ} F · G(carry, [·/p], [·/p]) = Σ_{B_s×B_s×δ'} (level-1 cell sum of F) · G`. -/
lemma regroup (s l l' : ℕ) (F G : ℕ → ℕ → ℕ → ℤ_[p]) :
    ∑ q ∈ blk p (s + 1) l, ∑ q' ∈ blk p (s + 1) l', ∑ δ ∈ range 2,
        F δ q q' * G (cry p 1 q q' δ) (q / p) (q' / p)
      = ∑ q₁ ∈ blk p s l, ∑ q₁' ∈ blk p s l', ∑ δ' ∈ range 2,
          cellSum p F 1 q₁ q₁' δ' * G δ' q₁ q₁' := by
  have hm : ∀ (l : ℕ) (f : ℕ → ℤ_[p]),
      ∑ q ∈ blk p (s + 1) l, f q = ∑ q₁ ∈ blk p s l, ∑ q ∈ blk p 1 q₁, f q := by
    intro l f; rw [blk_merge p 1 s l f, Nat.add_comm]
  rw [hm l]
  apply Finset.sum_congr rfl; intro q₁ _
  simp_rw [hm l']
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q₁' _
  have hpt : ∀ q ∈ blk p 1 q₁, ∀ q' ∈ blk p 1 q₁', ∀ δ ∈ range 2,
      F δ q q' * G (cry p 1 q q' δ) (q / p) (q' / p)
        = ∑ δ' ∈ range 2, (if cry p 1 q q' δ = δ' then F δ q q' else 0) * G δ' q₁ q₁' := by
    intro q hq q' hq' δ _
    rw [div_of_mem_blk_one p hq, div_of_mem_blk_one p hq']
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq,
      if_pos (Finset.mem_range.mpr (by have := cry_le_one p 1 q q' δ; omega))]
  rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun q' hq' =>
    Finset.sum_congr rfl (fun δ hδ => hpt q hq q' hq' δ hδ)))]
  rw [sum_comm3]
  apply Finset.sum_congr rfl; intro δ' _
  unfold cellSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro q' _
  rw [Finset.sum_mul]

lemma cell_succ (hp : 0 < p) (a : ℕ → ℕ → ℕ → ℤ_[p]) (t i i' c : ℕ) :
    cellSum p (fun δ' q₁ q₁' => cellSum p a 1 q₁ q₁' δ') t i i' c = cellSum p a (t + 1) i i' c := by
  have h := regroup p t i i' a (fun δ' q₁ q₁' => if cry p t q₁ q₁' δ' = c then (1 : ℤ_[p]) else 0)
  beta_reduce at h
  have lhs : cellSum p (fun δ' q₁ q₁' => cellSum p a 1 q₁ q₁' δ') t i i' c
      = ∑ q₁ ∈ blk p t i, ∑ q₁' ∈ blk p t i', ∑ δ' ∈ range 2,
          cellSum p a 1 q₁ q₁' δ' * (if cry p t q₁ q₁' δ' = c then (1 : ℤ_[p]) else 0) := by
    unfold cellSum
    apply Finset.sum_congr rfl; intro q₁ _
    apply Finset.sum_congr rfl; intro q₁' _
    apply Finset.sum_congr rfl; intro δ' _
    split_ifs <;> simp
  rw [lhs, ← h]
  unfold cellSum
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro q' _
  apply Finset.sum_congr rfl; intro δ hδ
  rw [← cry_succ p hp t q q' δ (Finset.mem_range.mp hδ)]
  split_ifs <;> simp

/-- **Lemma 3.2** (scaled form). -/
theorem block_ind2 (T : ℕ → ℕ → ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u ≤ s → ∀ δ, δ < 2 → ∀ q q',
      (p : ℤ_[p]) ^ u ∣ T u δ q q' - T (u - 1) (cry p 1 q q' δ) (q / p) (q' / p))
    (a : ℕ → ℕ → ℕ → ℤ_[p])
    (ha : ∀ t, t ≤ s → ∀ i i' c, (p : ℤ_[p]) ^ (t + e) ∣ cellSum p a t i i' c) (l l' : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣
      ∑ q ∈ blk p s l, ∑ q' ∈ blk p s l', ∑ δ ∈ range 2, a δ q q' * T s δ q q' := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have key : ∀ s', s' ≤ s → ∀ (e : ℕ) (a : ℕ → ℕ → ℕ → ℤ_[p]),
      (∀ t, t ≤ s' → ∀ i i' c, (p : ℤ_[p]) ^ (t + e) ∣ cellSum p a t i i' c) →
      ∀ l l', (p : ℤ_[p]) ^ (s' + e) ∣
        ∑ q ∈ blk p s' l, ∑ q' ∈ blk p s' l', ∑ δ ∈ range 2, a δ q q' * T s' δ q q' := by
    intro s'
    induction s' with
    | zero =>
      intro _ e a ha l l'
      rw [blk_zero, blk_zero, Finset.sum_singleton, Finset.sum_singleton]
      apply Finset.dvd_sum; intro δ hδ
      have h := ha 0 le_rfl l l' δ
      rw [cell_zero p a l l' δ (Finset.mem_range.mp hδ)] at h
      exact h.mul_right _
    | succ s ih =>
    intro hss e a ha l l'
    have ha0 : ∀ δ, δ < 2 → ∀ q q', (p : ℤ_[p]) ^ e ∣ a δ q q' := by
      intro δ hδ q q'
      have h := ha 0 (by omega) q q' δ
      rwa [cell_zero p a q q' δ hδ, zero_add] at h
    have e1 : ∑ q ∈ blk p (s + 1) l, ∑ q' ∈ blk p (s + 1) l', ∑ δ ∈ range 2,
          a δ q q' * T (s + 1) δ q q'
        = ∑ q ∈ blk p (s + 1) l, ∑ q' ∈ blk p (s + 1) l', ∑ δ ∈ range 2,
            a δ q q' * (T (s + 1) δ q q' - T s (cry p 1 q q' δ) (q / p) (q' / p))
          + ∑ q ∈ blk p (s + 1) l, ∑ q' ∈ blk p (s + 1) l', ∑ δ ∈ range 2,
            a δ q q' * T s (cry p 1 q q' δ) (q / p) (q' / p) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro q _
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro q' _
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro δ _
      ring
    rw [e1, regroup p s l l' a (T s)]
    apply dvd_add
    · apply Finset.dvd_sum; intro q _
      apply Finset.dvd_sum; intro q' _
      apply Finset.dvd_sum; intro δ hδ
      have h1 := hT (s + 1) (by omega) hss δ (Finset.mem_range.mp hδ) q q'
      rw [Nat.add_sub_cancel] at h1
      rw [show s + 1 + e = e + (s + 1) by ring, pow_add]
      exact mul_dvd_mul (ha0 δ (Finset.mem_range.mp hδ) q q') h1
    · have ha' : ∀ t, t ≤ s → ∀ i i' c, (p : ℤ_[p]) ^ (t + (e + 1)) ∣
          cellSum p (fun δ' q₁ q₁' => cellSum p a 1 q₁ q₁' δ') t i i' c := by
        intro t ht i i' c
        rw [cell_succ p hp0, show t + (e + 1) = (t + 1) + e by ring]
        exact ha (t + 1) (by omega) i i' c
      have h := ih (by omega) (e + 1) (fun δ' q₁ q₁' => cellSum p a 1 q₁ q₁' δ') ha' l l'
      rwa [show s + (e + 1) = s + 1 + e by ring] at h
  exact key s le_rfl e a ha l l'

/-- Lemma 3.2 in the form used in §§4–6: top-level weights carry the label `δ = 0` only, the
top kernel is a single function `F`, and its tower congruence is only needed where the weight is
nonzero. -/
theorem block_ind2_top (T : ℕ → ℕ → ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u < s → ∀ δ, δ < 2 → ∀ q q',
      (p : ℤ_[p]) ^ u ∣ T u δ q q' - T (u - 1) (cry p 1 q q' δ) (q / p) (q' / p))
    (F : ℕ → ℕ → ℤ_[p]) (a : ℕ → ℕ → ℤ_[p])
    (hF : ∀ q q', a q q' = 0 ∨
      (p : ℤ_[p]) ^ s ∣ F q q' - T (s - 1) (cry p 1 q q' 0) (q / p) (q' / p))
    (ha : ∀ t, t ≤ s → ∀ i i' c, (p : ℤ_[p]) ^ (t + e) ∣
      ∑ q ∈ blk p t i, ∑ q' ∈ blk p t i', if cry p t q q' 0 = c then a q q' else 0)
    (l l' : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣ ∑ q ∈ blk p s l, ∑ q' ∈ blk p s l', a q q' * F q q' := by
  set T' : ℕ → ℕ → ℕ → ℕ → ℤ_[p] := fun u δ q q' =>
    if u < s then T u δ q q' else T (s - 1) (cry p 1 q q' δ) (q / p) (q' / p) with hT'
  set a' : ℕ → ℕ → ℕ → ℤ_[p] := fun δ q q' => if δ = 0 then a q q' else 0 with ha'
  have hT'tower : ∀ u, 1 ≤ u → u ≤ s → ∀ δ, δ < 2 → ∀ q q',
      (p : ℤ_[p]) ^ u ∣ T' u δ q q' - T' (u - 1) (cry p 1 q q' δ) (q / p) (q' / p) := by
    intro u hu1 hu δ hδ q q'
    rcases Nat.lt_or_ge u s with hlt | hge
    · simp only [hT', if_pos hlt, if_pos (show u - 1 < s by omega)]
      exact hT u hu1 hlt δ hδ q q'
    · have hus : u = s := le_antisymm hu hge
      subst hus
      simp only [hT', lt_irrefl, if_false, if_pos (show u - 1 < u by omega), sub_self]
      exact dvd_zero _
  have hcell : ∀ t i i' c, cellSum p a' t i i' c = ∑ q ∈ blk p t i, ∑ q' ∈ blk p t i',
      if cry p t q q' 0 = c then a q q' else 0 := by
    intro t i i' c
    unfold cellSum
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro q' _
    simp [ha', Finset.sum_range_succ]
  have ha0 : ∀ q q', (p : ℤ_[p]) ^ e ∣ a q q' := by
    intro q q'
    have h := ha 0 (by omega) q q' 0
    rw [← hcell, cell_zero p a' q q' 0 (by norm_num), zero_add] at h
    simpa [ha'] using h
  have e1 : ∑ q ∈ blk p s l, ∑ q' ∈ blk p s l', a q q' * F q q'
      = ∑ q ∈ blk p s l, ∑ q' ∈ blk p s l', a q q' * (F q q' - T' s 0 q q')
        + ∑ q ∈ blk p s l, ∑ q' ∈ blk p s l', ∑ δ ∈ range 2, a' δ q q' * T' s δ q q' := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro q _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro q' _
    have h2 : ∑ δ ∈ range 2, a' δ q q' * T' s δ q q' = a q q' * T' s 0 q q' := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; simp [ha']
    rw [h2]; ring
  rw [e1]
  refine dvd_add (Finset.dvd_sum fun q _ => Finset.dvd_sum fun q' _ => ?_)
    (block_ind2 p T' s e hT'tower a' (fun t ht i i' c => by rw [hcell]; exact ha t ht i i' c) l l')
  rcases hF q q' with h0 | hk
  · rw [h0, zero_mul]; exact dvd_zero _
  · have hTs : T' s 0 q q' = T (s - 1) (cry p 1 q q' 0) (q / p) (q' / p) := by
      simp only [hT', lt_irrefl, if_false]
    rw [hTs, add_comm, pow_add]
    exact mul_dvd_mul (ha0 q q') hk

theorem block_ind2_top_range (T : ℕ → ℕ → ℕ → ℕ → ℤ_[p]) (s e : ℕ)
    (hT : ∀ u, 1 ≤ u → u < s → ∀ δ, δ < 2 → ∀ q q',
      (p : ℤ_[p]) ^ u ∣ T u δ q q' - T (u - 1) (cry p 1 q q' δ) (q / p) (q' / p))
    (F : ℕ → ℕ → ℤ_[p]) (a : ℕ → ℕ → ℤ_[p])
    (hF : ∀ q q', a q q' = 0 ∨
      (p : ℤ_[p]) ^ s ∣ F q q' - T (s - 1) (cry p 1 q q' 0) (q / p) (q' / p))
    (ha : ∀ t, t ≤ s → ∀ i i' c, (p : ℤ_[p]) ^ (t + e) ∣
      ∑ q ∈ blk p t i, ∑ q' ∈ blk p t i', if cry p t q q' 0 = c then a q q' else 0)
    (M M' : ℕ) :
    (p : ℤ_[p]) ^ (s + e) ∣
      ∑ q ∈ range (M * p ^ s), ∑ q' ∈ range (M' * p ^ s), a q q' * F q q' := by
  rw [sum_range_blk]
  apply Finset.dvd_sum; intro l _
  rw [Finset.sum_congr rfl (fun q _ => sum_range_blk p s M' (fun q' => a q q' * F q q')),
    Finset.sum_comm]
  apply Finset.dvd_sum; intro l' _
  exact block_ind2_top p T s e hT F a hF ha l l'

/- ### Kernels -/

def St (N k j : ℕ) : ℕ :=
  (N - 1).choose k ^ 2 * (N + k - 1).choose k * (N - 1).choose (k + j) ^ 2 * (N + j - 1).choose j

def Psi (L n j : ℕ) : ℕ :=
  (L - 1).choose n ^ 2 * (L + n).choose n * (L - 1).choose (n + j) ^ 2 * (L + j - 1).choose j

def Kk (L n : ℕ) : ℕ := ∑ j ∈ range L, Psi L n j

def Xi (L δ q q' : ℕ) : ℕ :=
  (L - 1).choose q ^ 2 * (L + q).choose q * (L - 1).choose (q + q' + δ) ^ 2 * (L + q').choose q'

def Xih (L n j : ℕ) : ℕ :=
  (L - 1).choose n ^ 2 * (L + n).choose n * (L - 1).choose (n + j) ^ 2 * (L + j - 1).choose (j - 1)

noncomputable def Kw (L n : ℕ) (g : ℕ → ℤ_[p]) : ℤ_[p] := ∑ j ∈ range L, (Psi L n j : ℤ_[p]) * g j

/-- `ρ_u(n, j₁) = H′_n - H′_{p j₁} + 2 H′_{n + p j₁}` (independent of `u`). -/
noncomputable def rho (n j : ℕ) : ℤ_[p] := H p n - H p (p * j) + 2 * H p (n + p * j)

/- ### Lemma 3.3 (how the terms factor) -/

omit [Fact p.Prime] in
lemma choose_absorb (N k : ℕ) (hN : 1 ≤ N) :
    (N + k) * (N + k - 1).choose k = N * (N + k).choose k := by
  have h := Nat.add_one_mul_choose_eq (N + k - 1) (N - 1)
  rw [show N + k - 1 + 1 = N + k by omega, show N - 1 + 1 = N by omega] at h
  rw [Epoch361883.choose_symm_index N k hN, Nat.choose_symm_add] at h
  rw [h, mul_comm]

omit [Fact p.Prime] in
/-- **Lemma 3.3**: `S̃(N;k,j) = N/(N+k) Ψ_r(k,j)` (with `L_r = N`), multiplied out. -/
theorem St_factor (N k j : ℕ) (hN : 1 ≤ N) : (N + k) * St N k j = N * Psi N k j := by
  unfold St Psi
  have h := choose_absorb N k hN
  calc (N + k) * ((N - 1).choose k ^ 2 * (N + k - 1).choose k * (N - 1).choose (k + j) ^ 2
        * (N + j - 1).choose j)
      = ((N + k) * (N + k - 1).choose k) * ((N - 1).choose k ^ 2 * (N - 1).choose (k + j) ^ 2
        * (N + j - 1).choose j) := by ring
    _ = (N * (N + k).choose k) * ((N - 1).choose k ^ 2 * (N - 1).choose (k + j) ^ 2
        * (N + j - 1).choose j) := by rw [h]
    _ = _ := by ring

omit [Fact p.Prime] in
lemma choose_absorb_pred (L j : ℕ) (hj : 1 ≤ j) :
    j * (L + j - 1).choose j = L * (L + j - 1).choose (j - 1) := by
  have h := Nat.choose_succ_right_eq (L + j - 1) (j - 1)
  rw [show j - 1 + 1 = j by omega, show L + j - 1 - (j - 1) = L by omega] at h
  rw [mul_comm, h, mul_comm]

omit [Fact p.Prime] in
/-- **Lemma 3.3**: `Ψ_u(n,j) = (L_u/j) Ξ̂_u(n,j)`, multiplied out (`j ≥ 1`). -/
theorem Psi_factor (L n j : ℕ) (hj : 1 ≤ j) : j * Psi L n j = L * Xih L n j := by
  unfold Psi Xih
  have h := choose_absorb_pred L j hj
  calc j * ((L - 1).choose n ^ 2 * (L + n).choose n * (L - 1).choose (n + j) ^ 2
        * (L + j - 1).choose j)
      = (j * (L + j - 1).choose j) * ((L - 1).choose n ^ 2 * (L + n).choose n
        * (L - 1).choose (n + j) ^ 2) := by ring
    _ = (L * (L + j - 1).choose (j - 1)) * ((L - 1).choose n ^ 2 * (L + n).choose n
        * (L - 1).choose (n + j) ^ 2) := by rw [h]
    _ = _ := by ring

omit [Fact p.Prime] in
lemma Psi_eq_zero (L n j : ℕ) (hL : 1 ≤ L) (h : L ≤ n + j) : Psi L n j = 0 := by
  unfold Psi
  rw [Nat.choose_eq_zero_of_lt (by omega : L - 1 < n + j)]
  ring

/- ### Lemma 3.4 (towers) -/

omit [Fact p.Prime] in
lemma dvd_mul4_sub {R : Type*} [CommRing R] {d a1 a2 a3 a4 b1 b2 b3 b4 : R}
    (h1 : d ∣ a1 - b1) (h2 : d ∣ a2 - b2) (h3 : d ∣ a3 - b3) (h4 : d ∣ a4 - b4) :
    d ∣ a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4 := by
  have e : a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4
      = (a1 - b1) * (a2 * a3 * a4) + b1 * ((a2 - b2) * (a3 * a4))
        + b1 * b2 * ((a3 - b3) * a4) + b1 * b2 * b3 * (a4 - b4) := by ring
  rw [e]
  exact dvd_add (dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_left _))
    ((h3.mul_right _).mul_left _)) (h4.mul_left _)

/-- Lemma 3.4(a), unscaled `j`: `Ψ_u(q,j) ≡ 0 (mod p^u)` for `p ∤ j`. -/
theorem Psi_unscaled (m u q j : ℕ) (hj : ¬ p ∣ j) :
    (p : ℤ_[p]) ^ u ∣ ((Psi (m * p ^ u) q j : ℕ) : ℤ_[p]) := by
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => hj (h ▸ dvd_zero p))
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (Psi_factor (m * p ^ u) q j hj1)
  push_cast at h
  have h2 : (p : ℤ_[p]) ^ u ∣ (j : ℤ_[p]) * ((Psi (m * p ^ u) q j : ℕ) : ℤ_[p]) := by
    rw [h]; exact ⟨(m : ℤ_[p]) * (Xih (m * p ^ u) q j : ℤ_[p]), by ring⟩
  exact (IsUnit.dvd_mul_left (Epoch361883.isUnit_nat_of_not_dvd p hj)).mp h2

/-- Lemma 3.4(a), scaled `j`: `Ψ_u(q, p j₁) ≡ Ψ_{u-1}([q/p], j₁) (mod p^u)`. -/
theorem Psi_tower (m u q j : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) :
    (p : ℤ_[p]) ^ u ∣ ((Psi (m * p ^ u) q (p * j) : ℕ) : ℤ_[p])
      - ((Psi (m * p ^ (u - 1)) (q / p) j : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold Psi
  push_cast
  have h3 := cong_sq_pred p m u (q + p * j) hm hu
  rw [Nat.add_mul_div_left q j hp0] at h3
  exact dvd_mul4_sub (cong_sq_pred p m u q hm hu) (cong_add p m u q hu) h3
    (cong_add_pred p m u j hu)

lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (p * N), f k
      = ∑ j ∈ range N, f (p * j) + ∑ k ∈ (range (p * N)).filter (fun k => ¬ p ∣ k), f k := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * N)) (fun k => p ∣ k)]
  congr 1
  have himg : (range (p * N)).filter (fun k => p ∣ k) = (range N).image (fun j => p * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, ⟨j, rfl⟩⟩
      exact ⟨j, Nat.lt_of_mul_lt_mul_left hk, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hj hp0, dvd_mul_right p j⟩
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hp0 hxy

/-- Lemma 3.4(a)/(c)/(d), general weight: `Σ_j Ψ_u(q,j) g(j) ≡ Σ_{j₁} Ψ_{u-1}([q/p],j₁) g(p j₁)`. -/
theorem Kw_tower (m u q : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) (g : ℕ → ℤ_[p]) :
    (p : ℤ_[p]) ^ u ∣ Kw p (m * p ^ u) q g - Kw p (m * p ^ (u - 1)) (q / p) (fun j => g (p * j)) := by
  unfold Kw
  rw [mul_pow_pred p m u hu, sum_range_mul_split]
  have e : ∑ j ∈ range (m * p ^ (u - 1)), ((Psi (p * (m * p ^ (u - 1))) q (p * j) : ℕ) : ℤ_[p]) * g (p * j)
        + ∑ k ∈ (range (p * (m * p ^ (u - 1)))).filter (fun k => ¬ p ∣ k),
          ((Psi (p * (m * p ^ (u - 1))) q k : ℕ) : ℤ_[p]) * g k
        - ∑ j ∈ range (m * p ^ (u - 1)), ((Psi (m * p ^ (u - 1)) (q / p) j : ℕ) : ℤ_[p]) * g (p * j)
      = ∑ j ∈ range (m * p ^ (u - 1)), (((Psi (p * (m * p ^ (u - 1))) q (p * j) : ℕ) : ℤ_[p])
          - ((Psi (m * p ^ (u - 1)) (q / p) j : ℕ) : ℤ_[p])) * g (p * j)
        + ∑ k ∈ (range (p * (m * p ^ (u - 1)))).filter (fun k => ¬ p ∣ k),
          ((Psi (p * (m * p ^ (u - 1))) q k : ℕ) : ℤ_[p]) * g k := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hL : p * (m * p ^ (u - 1)) = m * p ^ u := (mul_pow_pred p m u hu).symm
  rw [hL]
  apply dvd_add
  · apply Finset.dvd_sum; intro j _
    exact (Psi_tower p m u q j hm hu).mul_right _
  · apply Finset.dvd_sum; intro k hk
    exact (Psi_unscaled p m u q k (Finset.mem_filter.mp hk).2).mul_right _

/-- **Lemma 3.4(a)**: `K_u(q) ≡ K_{u-1}([q/p]) (mod p^u)`. -/
theorem Kk_tower (m u q : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) :
    (p : ℤ_[p]) ^ u ∣ ((Kk (m * p ^ u) q : ℕ) : ℤ_[p]) - ((Kk (m * p ^ (u - 1)) (q / p) : ℕ) : ℤ_[p]) := by
  have h := Kw_tower p m u q hm hu (fun _ => 1)
  unfold Kw at h
  unfold Kk
  push_cast
  simpa using h

/-- **Lemma 3.4(b)**: `Ξ_u^{(δ)}(q,q') ≡ Ξ_{u-1}^{(δ')}([q/p],[q'/p]) (mod p^u)`. -/
theorem Xi_tower (m u δ q q' : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) (hδ : δ < 2) :
    (p : ℤ_[p]) ^ u ∣ ((Xi (m * p ^ u) δ q q' : ℕ) : ℤ_[p])
      - ((Xi (m * p ^ (u - 1)) (cry p 1 q q' δ) (q / p) (q' / p) : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold Xi
  push_cast
  have h3 := cong_sq_pred p m u (q + q' + δ) hm hu
  rw [add_div_cry p hp0 q q' δ hδ] at h3
  exact dvd_mul4_sub (cong_sq_pred p m u q hm hu) (cong_add p m u q hu) h3 (cong_add p m u q' hu)

/-- **Lemma 3.4(b)**: for `p ∤ j`, `Ξ̂_u(n,j) ≡ Ξ_{u-1}^{(δ)}([n/p],[j/p]) (mod p^u)`. -/
theorem Xih_tower (m u n j : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) (hj : ¬ p ∣ j) :
    (p : ℤ_[p]) ^ u ∣ ((Xih (m * p ^ u) n j : ℕ) : ℤ_[p])
      - ((Xi (m * p ^ (u - 1)) (cry p 1 n j 0) (n / p) (j / p) : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold Xih Xi
  push_cast
  have h3 := cong_sq_pred p m u (n + j) hm hu
  have hd := add_div_cry p hp0 n j 0 (by norm_num)
  rw [Nat.add_zero] at hd
  rw [hd] at h3
  exact dvd_mul4_sub (cong_sq_pred p m u n hm hu) (cong_add p m u n hu) h3
    (cong_add_pred_pred p m u j hu hj)

/-- **Lemma 3.4(c)** (moment kernels): `Σ_j j^t Ψ_u(q,j) ≡ 0 (mod p^u)` for `t ≥ 1`. -/
theorem moment_dvd (m u q t : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ_[p]) ^ u ∣ Kw p (m * p ^ u) q (fun j => (j : ℤ_[p]) ^ t) := by
  induction u generalizing q with
  | zero => simp
  | succ u ih =>
    have h := Kw_tower p m (u + 1) q hm (by omega) (fun j => (j : ℤ_[p]) ^ t)
    rw [Nat.add_sub_cancel] at h
    have e : Kw p (m * p ^ u) (q / p) (fun j => (((p * j : ℕ)) : ℤ_[p]) ^ t)
        = (p : ℤ_[p]) ^ t * Kw p (m * p ^ u) (q / p) (fun j => (j : ℤ_[p]) ^ t) := by
      unfold Kw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      push_cast; ring
    rw [e] at h
    have h2 : (p : ℤ_[p]) ^ (u + 1) ∣ (p : ℤ_[p]) ^ t * Kw p (m * p ^ u) (q / p) (fun j => (j : ℤ_[p]) ^ t) := by
      rw [show u + 1 = 1 + u by ring, pow_add]
      exact mul_dvd_mul (pow_dvd_pow _ ht) (ih (q / p))
    have := dvd_add h h2
    rwa [sub_add_cancel] at this

/-- **Lemma 3.4(d)** (harmonically weighted kernels):
`K̃_u^{(d)}(q) ≡ K̃_{u-1}^{(d+1)}([q/p]) (mod p^u)`. -/
theorem Khar_tower (m u q d : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) :
    (p : ℤ_[p]) ^ u ∣ Kw p (m * p ^ u) q (fun j => H p (p ^ d * j))
      - Kw p (m * p ^ (u - 1)) (q / p) (fun j => H p (p ^ (d + 1) * j)) := by
  have h := Kw_tower p m u q hm hu (fun j => H p (p ^ d * j))
  have e : (fun j => H p (p ^ d * (p * j))) = (fun j => H p (p ^ (d + 1) * j)) := by
    funext j; rw [show p ^ d * (p * j) = p ^ (d + 1) * j by ring]
  beta_reduce at h
  rwa [e] at h

/- ### Lemma 3.5 (one-level first-order model) -/

/-- **Lemma 3.5** (exact): `Ψ_{u+1}(n, p j₁) = Ψ_u([n/p], j₁) P_n² P̄_n P_{n+pj₁}² P̄_{pj₁}`,
`L = m p^(u+1)`. -/
theorem Psi_exact (m u n j : ℕ) (hm : 1 ≤ m) :
    ((Psi (m * p ^ (u + 1)) n (p * j) : ℕ) : ℤ_[p])
      = ((Psi (m * p ^ u) (n / p) j : ℕ) : ℤ_[p])
        * (Pm p ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) n ^ 2 * Pp p ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) n
          * Pm p ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) (n + p * j) ^ 2
          * Pp p ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) (p * j)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 := choose_pred_prod p m (u + 1) n hm (by omega)
  have h2 := choose_add_prod p m (u + 1) n (by omega)
  have h3 := choose_pred_prod p m (u + 1) (n + p * j) hm (by omega)
  have h4 := choose_add_pred_prod p m (u + 1) (p * j) (by omega) (dvd_mul_right p j)
  rw [Nat.add_sub_cancel] at h1 h2 h3 h4
  rw [Nat.add_mul_div_left n j hp0] at h3
  rw [Nat.mul_div_cancel_left j hp0] at h4
  have hsq : ∀ k : ℕ, ((-1 : ℤ_[p]) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set L := ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) with hL
  unfold Psi
  push_cast
  rw [h1, h2, h3, h4]
  linear_combination
    ((((m * p ^ u - 1).choose (n / p) : ℕ) : ℤ_[p]) * Pm p L n) ^ 2
      * ((((m * p ^ u + n / p).choose (n / p) : ℕ) : ℤ_[p]) * Pp p L n)
      * ((((m * p ^ u + j - 1).choose j : ℕ) : ℤ_[p]) * Pp p L (p * j))
      * ((((m * p ^ u - 1).choose (n / p + j) : ℕ) : ℤ_[p]) * Pm p L (n + p * j)) ^ 2
      * (((-1 : ℤ_[p]) ^ (n + p * j - (n / p + j))) ^ 2 * hsq (n - n / p)
        + hsq (n + p * j - (n / p + j)))

/-- **Lemma 3.5**: `Ψ_{u+1}(n, p j₁) ≡ Ψ_u([n/p], j₁)(1 - L ρ_u(n, j₁)) (mod p^(2u+2))`. -/
theorem Psi_fo (m u n j : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (2 * u + 2) ∣ ((Psi (m * p ^ (u + 1)) n (p * j) : ℕ) : ℤ_[p])
      - ((Psi (m * p ^ u) (n / p) j : ℕ) : ℤ_[p])
        * (1 - ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) * rho p n j) := by
  rw [Psi_exact p m u n j hm]
  set L := ((m * p ^ (u + 1) : ℕ) : ℤ_[p]) with hL
  have hE := fo_mul (fo_mul (fo_mul (fo_pow (Pm_fo p L n) 2) (Pp_fo p L n))
    (fo_pow (Pm_fo p L (n + p * j)) 2)) (Pp_fo p L (p * j))
  set E := Pm p L n ^ 2 * Pp p L n * Pm p L (n + p * j) ^ 2 * Pp p L (p * j) with hEdef
  have he : ((2 : ℕ) : ℤ_[p]) * -H p n + H p n + ((2 : ℕ) : ℤ_[p]) * -H p (n + p * j) + H p (p * j)
      = -rho p n j := by unfold rho; push_cast; ring
  rw [he] at hE
  have hL2 : (p : ℤ_[p]) ^ (2 * u + 2) ∣ L ^ 2 := by
    rw [hL, show 2 * u + 2 = (u + 1) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd (ppow_dvd_cast p m (u + 1)) 2
  have e : ((Psi (m * p ^ u) (n / p) j : ℕ) : ℤ_[p]) * E
      - ((Psi (m * p ^ u) (n / p) j : ℕ) : ℤ_[p]) * (1 - L * rho p n j)
      = ((Psi (m * p ^ u) (n / p) j : ℕ) : ℤ_[p]) * (E - 1 - L * -rho p n j) := by ring
  rw [e]
  exact (hL2.trans hE).mul_left _

end block

end ShiftLib
