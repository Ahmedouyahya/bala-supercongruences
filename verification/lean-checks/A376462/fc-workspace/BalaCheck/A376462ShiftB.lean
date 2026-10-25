import BalaCheck.A376462ShiftRep

/-!
# A376462 shifted congruence, part 4: class B (§6)

Proof note: `proofs/A376462-shifted-congruence.md`, §6. For `p ∤ k`, `p ∤ j`,
`S̃(N;k,j) = N² (N+k)⁻¹ j⁻¹ Ξ̂_r(k,j)` (Lemma 3.3 twice), `(N+k)⁻¹ ≡ k⁻¹ (mod p^r)`, and
`Σ′_{k,j} Ξ̂_r(k,j)/(kj) ≡ 0 (mod p^r)` by Lemma 3.2 with the cell sums of Lemma 2.7(B).
-/

open Nat Finset

namespace A376462Shift

open ShiftLib

section padic

variable (p : ℕ) [Fact p.Prime]

/-- **Class B** (§6): `Σ_B ≡ 0 (mod p^(3r))`. -/
theorem classB (hp5 : 5 ≤ p) (m w : ℕ) (hm : 1 ≤ m) :
    (p : ℤ_[p]) ^ (3 * (w + 1)) ∣ ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
      ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
        ((St (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hN : 1 ≤ m * p ^ (w + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpN : p ∣ m * p ^ (w + 1) := ⟨m * p ^ w, by ring⟩
  have hpN' : p ^ (w + 1) ∣ m * p ^ (w + 1) := Dvd.intro_left _ rfl
  have e1 : ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
      ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
        ((St (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])
      = ∑ k ∈ range (m * p ^ (w + 1)), ∑ j ∈ range (m * p ^ (w + 1)),
          ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * (Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p])
            * Ring.inverse (j : ℤ_[p]) * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])) := by
    calc _ = ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
          ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j),
            ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * (Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p])
              * Ring.inverse (j : ℤ_[p]) * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])) := by
          apply Finset.sum_congr rfl; intro k hk
          apply Finset.sum_congr rfl; intro j hj
          rw [St_eq_K p _ k j hN hpN (Finset.mem_filter.mp hk).2,
            Psi_eq_unsc p _ k j (Finset.mem_filter.mp hj).2]
          ring
      _ = ∑ k ∈ (range (m * p ^ (w + 1))).filter (fun k => ¬ p ∣ k),
          ∑ j ∈ range (m * p ^ (w + 1)),
            ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * (Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p])
              * Ring.inverse (j : ℤ_[p]) * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])) := by
          apply Finset.sum_congr rfl; intro k _
          exact sum_filter_ndvd p _ _ (fun j hj => by rw [inv_eq_zero_of_dvd p hj]; ring)
      _ = _ := sum_filter_ndvd p _ _ (fun k hk => by
            rw [inv_add_eq_zero p hpN hk]; simp)
  have e2 : ∑ k ∈ range (m * p ^ (w + 1)), ∑ j ∈ range (m * p ^ (w + 1)),
          ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * (Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p])
            * Ring.inverse (j : ℤ_[p]) * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p]))
      = ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * ∑ k ∈ range (m * p ^ (w + 1)),
          ∑ j ∈ range (m * p ^ (w + 1)), Ring.inverse (k : ℤ_[p]) * Ring.inverse (j : ℤ_[p])
            * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])
        + ∑ k ∈ range (m * p ^ (w + 1)), ∑ j ∈ range (m * p ^ (w + 1)),
          ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) ^ 2 * ((Ring.inverse ((m * p ^ (w + 1) + k : ℕ) : ℤ_[p])
            - Ring.inverse (k : ℤ_[p])) * Ring.inverse (j : ℤ_[p])
              * ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [e1, e2]
  have hF : ∀ q q' : ℕ, (fun k j => Ring.inverse (k : ℤ_[p]) * Ring.inverse (j : ℤ_[p])) q q' = 0 ∨
      (p : ℤ_[p]) ^ (w + 1) ∣ (fun k j => ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p])) q q'
        - (fun u δ q q' => ((Xi (m * p ^ u) δ q q' : ℕ) : ℤ_[p])) (w + 1 - 1)
            (cry p 1 q q' 0) (q / p) (q' / p) := by
    intro q q'
    by_cases hq' : p ∣ q'
    · left; simp [inv_eq_zero_of_dvd p hq']
    · right; exact Xih_tower p m (w + 1) q q' hm (by omega) hq'
  have hb := block_ind2_top_range p (fun u δ q q' => ((Xi (m * p ^ u) δ q q' : ℕ) : ℤ_[p]))
    (w + 1) 0 (fun u hu1 _ δ hδ q q' => Xi_tower p m u δ q q' hm hu1 hδ)
    (fun k j => ((Xih (m * p ^ (w + 1)) k j : ℕ) : ℤ_[p]))
    (fun k j => Ring.inverse (k : ℤ_[p]) * Ring.inverse (j : ℤ_[p])) hF
    (fun t _ i i' c => by rw [add_zero]; exact carry_B p hp5 t i i' c) m m
  rw [add_zero] at hb
  apply dvd_add
  · rw [show 3 * (w + 1) = (w + 1) * 2 + (w + 1) by ring, pow_add, pow_mul]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (ppow_dvd_cast p m (w + 1)) 2) hb
  · apply Finset.dvd_sum; intro k _
    apply Finset.dvd_sum; intro j _
    have h := inv_shift p (w + 1) (m * p ^ (w + 1)) k hpN'
    rw [show 3 * (w + 1) = (w + 1) * 2 + (w + 1) by ring, pow_add, pow_mul]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (ppow_dvd_cast p m (w + 1)) 2)
      ((h.mul_right _).mul_right _)

end padic

end A376462Shift
