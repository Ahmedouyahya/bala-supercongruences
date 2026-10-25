import BalaCheck.A376462ShiftK

/-!
# A376462 shifted congruence, part 3: classes K and J (§4, §5)

Proof note: `proofs/A376462-shifted-congruence.md`, §4 and §5.

* Class K: the kernel `Ψ` of Lemma 3.3 (`ShiftLib.Psi`), `kerK`; `classK`.
* Class J: the kernel `Φ_u(k,j) = C(L-1,k)² C(L+k-1,k) C(L-1,k+j)² C(L+j,j)` of §5 (`Phi`), with
  harmonic index `j` and kernel index `k`; its exact one-level identity `Phi_exact`
  (§5(ii), Lemma 1.1 factor by factor), first-order form `Phi_fo`, unscaled factorisation
  `Phi_factor` (§5(i)) and tower `Xihp_tower`; `kerJ`; `classJ`.
Both classes are then the generic `KerData.top` (`A376462ShiftK.lean`) times `N`.
-/

open Nat Finset

namespace A376462Shift

open ShiftLib

/-- `Φ_u(k,j)` of §5 (with `L = L_u`). -/
def Phi (L k j : ℕ) : ℕ :=
  (L - 1).choose k ^ 2 * (L + k - 1).choose k * (L - 1).choose (k + j) ^ 2 * (L + j).choose j

/-- `Ξ̂′_u(k,j)` of §5(i). -/
def Xihp (L k j : ℕ) : ℕ :=
  (L - 1).choose k ^ 2 * (L + k - 1).choose (k - 1) * (L - 1).choose (k + j) ^ 2 * (L + j).choose j

/-- `S̃(N;k,j) = N/(N+j) Φ_r(k,j)`, multiplied out. -/
theorem St_factorJ (N k j : ℕ) (hN : 1 ≤ N) : (N + j) * St N k j = N * Phi N k j := by
  have h := choose_absorb N j hN
  unfold St Phi
  rw [show (N + j) * ((N - 1).choose k ^ 2 * (N + k - 1).choose k * (N - 1).choose (k + j) ^ 2
      * (N + j - 1).choose j) = ((N + j) * (N + j - 1).choose j) * ((N - 1).choose k ^ 2
      * (N + k - 1).choose k * (N - 1).choose (k + j) ^ 2) by ring, h]
  ring

/-- §5(i): `Φ_u(k,j) = (L_u/k) Ξ̂′_u(k,j)`, multiplied out (`k ≥ 1`). -/
theorem Phi_factor (L k j : ℕ) (hk : 1 ≤ k) : k * Phi L k j = L * Xihp L k j := by
  have h := choose_absorb_pred L k hk
  unfold Phi Xihp
  rw [show k * ((L - 1).choose k ^ 2 * (L + k - 1).choose k * (L - 1).choose (k + j) ^ 2
      * (L + j).choose j) = (k * (L + k - 1).choose k) * ((L - 1).choose k ^ 2
      * (L - 1).choose (k + j) ^ 2 * (L + j).choose j) by ring, h]
  ring

section padic

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
lemma cry_comm (t a b δ : ℕ) : cry p t a b δ = cry p t b a δ := by
  unfold cry; rw [Nat.add_comm (a % p ^ t) (b % p ^ t)]

/-- Class J factorisation: `S̃(N;k,j) = N (N+j)⁻¹ Φ(N;k,j)` for `p ∤ j`. -/
lemma St_eq_J (N k j : ℕ) (hN : 1 ≤ N) (hpN : p ∣ N) (hj : ¬ p ∣ j) :
    ((St N k j : ℕ) : ℤ_[p])
      = (N : ℤ_[p]) * Ring.inverse ((N + j : ℕ) : ℤ_[p]) * ((Phi N k j : ℕ) : ℤ_[p]) := by
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (St_factorJ N k j hN)
  have hu := inv_mul_nat p (not_dvd_add p hpN hj)
  push_cast at h hu ⊢
  linear_combination (-((St N k j : ℕ) : ℤ_[p])) * hu + Ring.inverse ((N : ℤ_[p]) + j) * h

/-- `Φ_u(k,j) = L k⁻¹ Ξ̂′_u(k,j)` for `p ∤ k`. -/
lemma Phi_eq_unsc (L k j : ℕ) (hk : ¬ p ∣ k) :
    ((Phi L k j : ℕ) : ℤ_[p])
      = (L : ℤ_[p]) * Ring.inverse (k : ℤ_[p]) * ((Xihp L k j : ℕ) : ℤ_[p]) := by
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (Phi_factor L k j hk1)
  have hu := inv_mul_nat p hk
  push_cast at h
  linear_combination (-((Phi L k j : ℕ) : ℤ_[p])) * hu + Ring.inverse (k : ℤ_[p]) * h

/-- §5(ii) (exact): `Φ_{w+1}(p k₁, j) = Φ_w(k₁, [j/p]) P̄_{pk₁} P²_{pk₁} P²_{pk₁+j} P̄_j`. -/
theorem Phi_exact (m w k j : ℕ) (hm : 1 ≤ m) :
    ((Phi (m * p ^ (w + 1)) (p * k) j : ℕ) : ℤ_[p])
      = ((Phi (m * p ^ w) k (j / p) : ℕ) : ℤ_[p])
        * (Pm p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k) ^ 2
          * Pp p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k)
          * Pm p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) (p * k + j) ^ 2
          * Pp p ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) j) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 := choose_pred_prod p m (w + 1) (p * k) hm (by omega)
  have h2 := choose_add_pred_prod p m (w + 1) (p * k) (by omega) (dvd_mul_right p k)
  have h3 := choose_pred_prod p m (w + 1) (p * k + j) hm (by omega)
  have h4 := choose_add_prod p m (w + 1) j (by omega)
  rw [Nat.add_sub_cancel] at h1 h2 h3 h4
  rw [Nat.mul_div_cancel_left k hp0] at h1 h2
  rw [Nat.mul_add_div hp0 k j] at h3
  have hsq : ∀ k : ℕ, ((-1 : ℤ_[p]) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set L := ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) with hL
  unfold Phi
  push_cast
  rw [h1, h2, h3, h4]
  linear_combination
    ((((m * p ^ w - 1).choose k : ℕ) : ℤ_[p]) * Pm p L (p * k)) ^ 2
      * ((((m * p ^ w + k - 1).choose k : ℕ) : ℤ_[p]) * Pp p L (p * k))
      * ((((m * p ^ w + j / p).choose (j / p) : ℕ) : ℤ_[p]) * Pp p L j)
      * ((((m * p ^ w - 1).choose (k + j / p) : ℕ) : ℤ_[p]) * Pm p L (p * k + j)) ^ 2
      * (((-1 : ℤ_[p]) ^ (p * k + j - (k + j / p))) ^ 2 * hsq (p * k - k)
        + hsq (p * k + j - (k + j / p)))

/-- §5(ii): `Φ_{w+1}(p k₁, j) ≡ Φ_w(k₁,[j/p]) (1 - L ρ′(j,k₁)) (mod p^(2w+2))`,
`ρ′(j,k₁) = -H′_j + H′_{pk₁} + 2 H′_{j+pk₁}`. -/
theorem Phi_fo (m w k j : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (2 * w + 2) ∣ ((Phi (m * p ^ (w + 1)) (p * k) j : ℕ) : ℤ_[p])
      - ((Phi (m * p ^ w) k (j / p) : ℕ) : ℤ_[p])
        * (1 - ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
          * (-1 * H p j + 1 * H p (p * k) + 2 * H p (j + p * k))) := by
  rw [Phi_exact p m w k j hm]
  set L := ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) with hL
  have hE := fo_mul (fo_mul (fo_mul (fo_pow (Pm_fo p L (p * k)) 2) (Pp_fo p L (p * k)))
    (fo_pow (Pm_fo p L (p * k + j)) 2)) (Pp_fo p L j)
  have he : ((2 : ℕ) : ℤ_[p]) * -H p (p * k) + H p (p * k) + ((2 : ℕ) : ℤ_[p]) * -H p (p * k + j)
      + H p j = -(-1 * H p j + 1 * H p (p * k) + 2 * H p (j + p * k)) := by
    rw [Nat.add_comm (p * k) j]; push_cast; ring
  rw [he] at hE
  have hL2 : (p : ℤ_[p]) ^ (2 * w + 2) ∣ L ^ 2 := by
    rw [hL, show 2 * w + 2 = (w + 1) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd (ppow_dvd_cast p m (w + 1)) 2
  have e : ((Phi (m * p ^ w) k (j / p) : ℕ) : ℤ_[p])
        * (Pm p L (p * k) ^ 2 * Pp p L (p * k) * Pm p L (p * k + j) ^ 2 * Pp p L j)
      - ((Phi (m * p ^ w) k (j / p) : ℕ) : ℤ_[p])
        * (1 - L * (-1 * H p j + 1 * H p (p * k) + 2 * H p (j + p * k)))
      = ((Phi (m * p ^ w) k (j / p) : ℕ) : ℤ_[p])
        * (Pm p L (p * k) ^ 2 * Pp p L (p * k) * Pm p L (p * k + j) ^ 2 * Pp p L j - 1
          - L * -(-1 * H p j + 1 * H p (p * k) + 2 * H p (j + p * k))) := by ring
  rw [e]
  exact (hL2.trans hE).mul_left _

/-- §5(i): for `p ∤ k`, `Ξ̂′_u(k,j) ≡ Ξ^{(δ)}_{u-1}([k/p],[j/p]) (mod p^u)`. -/
theorem Xihp_tower (m u k j : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) (hk : ¬ p ∣ k) :
    (p : ℤ_[p]) ^ u ∣ ((Xihp (m * p ^ u) k j : ℕ) : ℤ_[p])
      - ((Xi (m * p ^ (u - 1)) (cry p 1 k j 0) (k / p) (j / p) : ℕ) : ℤ_[p]) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold Xihp Xi
  push_cast
  have h3 := cong_sq_pred p m u (k + j) hm hu
  have hd := add_div_cry p hp0 k j 0 (by norm_num)
  rw [Nat.add_zero] at hd
  rw [hd] at h3
  exact dvd_mul4_sub (cong_sq_pred p m u k hm hu) (cong_add_pred_pred p m u k hu hk) h3
    (cong_add p m u j hu)

variable {p} {m : ℕ}

/-- The class-K kernel package (`Ψ`, `Ξ̂`, `Ξ` of §3). -/
noncomputable def kerK (hm : 1 ≤ m) : KerData p m where
  Ψ u n j := ((Psi (m * p ^ u) n j : ℕ) : ℤ_[p])
  Ξ u n j := ((Xih (m * p ^ u) n j : ℕ) : ℤ_[p])
  T u δ q q' := ((Xi (m * p ^ u) δ q q' : ℕ) : ℤ_[p])
  c₁ := 1
  c₂ := -1
  c₃ := 2
  fo w n j := by
    have h := Psi_fo p m w n j hm
    have e : rho p n j = 1 * H p n + -1 * H p (p * j) + 2 * H p (n + p * j) := by
      unfold rho; ring
    rw [e] at h
    exact h
  unsc u n j hj := Psi_eq_unsc p (m * p ^ u) n j hj
  Ξtow u n j hu hj := Xih_tower p m u n j hm hu hj
  Ttow u hu δ hδ q q' := Xi_tower p m u δ q q' hm hu hδ

/-- The class-J kernel package: harmonic index `n = j` of `Φ`, kernel index `k`. -/
noncomputable def kerJ (hm : 1 ≤ m) : KerData p m where
  Ψ u n j := ((Phi (m * p ^ u) j n : ℕ) : ℤ_[p])
  Ξ u n j := ((Xihp (m * p ^ u) j n : ℕ) : ℤ_[p])
  T u δ q q' := ((Xi (m * p ^ u) δ q' q : ℕ) : ℤ_[p])
  c₁ := -1
  c₂ := 1
  c₃ := 2
  fo w n j := Phi_fo p m w j n hm
  unsc u n j hj := Phi_eq_unsc p (m * p ^ u) j n hj
  Ξtow u n j hu hj := by
    have h := Xihp_tower p m u j n hm hu hj
    rw [cry_comm p 1 j n 0] at h
    exact h
  Ttow u hu δ hδ q q' := by
    have h := Xi_tower p m u δ q' q hm hu hδ
    rw [cry_comm p 1 q' q δ] at h
    exact h

lemma kerK_Khat (hm : 1 ≤ m) (w n : ℕ) : (kerK (p := p) hm).Khat w n
    = ∑ j ∈ range (m * p ^ w), ((Psi (m * p ^ (w + 1)) n (p * j) : ℕ) : ℤ_[p]) := rfl

lemma kerJ_Khat (hm : 1 ≤ m) (w n : ℕ) : (kerJ (p := p) hm).Khat w n
    = ∑ k ∈ range (m * p ^ w), ((Phi (m * p ^ (w + 1)) (p * k) n : ℕ) : ℤ_[p]) := rfl

variable (p)

/-- **Class K** (§4): `Σ_K ≡ 0 (mod p^(3r))`. -/
theorem classK (hp5 : 5 ≤ p) (m w : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
      ∑ j ∈ range (m * p ^ w), ((St (m * p ^ (w + 1)) k (p * j) : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hN : 1 ≤ m * p ^ (w + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ (w + 1) := ⟨m * p ^ w, by ring⟩
  have e : ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
        ∑ j ∈ range (m * p ^ w), ((St (m * p ^ (w + 1)) k (p * j) : ℕ) : ℤ_[p])
      = ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * ∑ k ∈ range (m * p ^ (w + 1)),
          Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p]) * (kerK (p := p) hm).Khat w k := by
    rw [Finset.mul_sum, ← sum_filter_ndvd p (range (m * p ^ (w + 1))) _
      (fun k hk => by rw [inv_add_eq_zero p hpN hk]; ring)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [kerK_Khat, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [St_eq_K p _ k (p * j) hN hpN hk']
    ring
  rw [e, show 3 * (w + 1) = (w + 1) + (2 * w + 2) by ring, pow_add]
  exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) ((kerK (p := p) hm).top hp5 w)

/-- **Class J** (§5): `Σ_J ≡ 0 (mod p^(3r))`. -/
theorem classJ (hp5 : 5 ≤ p) (m w : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ∑ k ∈ range (m * p ^ w),
      ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
        ((St (m * p ^ (w + 1)) (p * k) j : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hN : 1 ≤ m * p ^ (w + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ (w + 1) := ⟨m * p ^ w, by ring⟩
  have e : ∑ k ∈ range (m * p ^ w), ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
        ((St (m * p ^ (w + 1)) (p * k) j : ℕ) : ℤ_[p])
      = ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * ∑ j ∈ range (m * p ^ (w + 1)),
          Ring.inverse ((m * p ^ (w + 1) + j : ℕ) : ℤ_[p]) * (kerJ (p := p) hm).Khat w j := by
    rw [Finset.sum_comm, Finset.mul_sum, ← sum_filter_ndvd p (range (m * p ^ (w + 1))) _
      (fun j hj => by rw [inv_add_eq_zero p hpN hj]; ring)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    rw [kerJ_Khat, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [St_eq_J p _ (p * k) j hN hpN hj']
    ring
  rw [e, show 3 * (w + 1) = (w + 1) + (2 * w + 2) by ring, pow_add]
  exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) ((kerJ (p := p) hm).top hp5 w)

end padic

end A376462Shift
