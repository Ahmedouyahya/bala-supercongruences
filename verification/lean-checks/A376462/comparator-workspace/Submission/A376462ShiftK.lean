import Submission.A376462ShiftRep

/-!
# A376462 shifted congruence, part 2: the kernel argument of classes K and J (§4, §5)

Proof note: `proofs/A376462-shifted-congruence.md`, §4 (class K) and §5 (class J).

Both classes run the same argument on a kernel `Ψ_u(n, j)` (`n` = harmonic index,
`j` = kernel index, level `u`, `L_u = m p^u`); `KerData` records the four properties used:
* `fo`   (Lemma 3.5 / §5(ii)): `Ψ_{w+1}(n, p j) ≡ Ψ_w([n/p], j) (1 - L_{w+1} ρ(n, j)) (mod p^(2w+2))`,
  `ρ(n,j) = c₁ H′_n + c₂ H′_{pj} + c₃ H′_{n+pj}`;
* `unsc` (Lemma 3.3 / §5(i)): for `p ∤ j`, `Ψ_u(n,j) = L_u j⁻¹ Ξ_u(n,j)`;
* `Ξtow`, `Ttow` (Lemma 3.4(b)): `Ξ_u` reduces to a two-index tower `T` with carries.
From these: the weighted kernel towers (Lemma 3.4(a),(c),(d): `Kg_tower`, `Kg_moment`, `Kg_har`),
the pieces `X₁, X₂, X₃, Y` of §4, the induction `A_0 ≡ … ≡ A_{r-1} ≡ 0` (`A_dvd`, in the general
form `p^(2σ+2s) ∣ A(s,σ) = Σ_{q < L_s} σ_σ(q) K_s(q)`), and the top-level statement `top`:
`p^(2r) ∣ Σ_{n < N} (N+n)⁻¹ K̂_r(n)`, `K̂_r(n) = Σ_{j₁ < M} Ψ_r(n, p j₁)`.
-/

open Nat Finset

namespace A376462Shift

open ShiftLib

/-- The kernel data of §§4–5 (see the module docstring). -/
structure KerData (p : ℕ) [Fact p.Prime] (m : ℕ) where
  Ψ : ℕ → ℕ → ℕ → ℤ_[p]
  Ξ : ℕ → ℕ → ℕ → ℤ_[p]
  T : ℕ → ℕ → ℕ → ℕ → ℤ_[p]
  c₁ : ℤ_[p]
  c₂ : ℤ_[p]
  c₃ : ℤ_[p]
  fo : ∀ w n j, (p : ℤ_[p]) ^ (2 * w + 2) ∣ Ψ (w + 1) n (p * j) - Ψ w (n / p) j *
      (1 - ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * (c₁ * H p n + c₂ * H p (p * j) + c₃ * H p (n + p * j)))
  unsc : ∀ u n j, ¬ p ∣ j →
      Ψ u n j = ((m * p ^ u : ℕ) : ℤ_[p]) * Ring.inverse (j : ℤ_[p]) * Ξ u n j
  Ξtow : ∀ u n j, 1 ≤ u → ¬ p ∣ j →
      (p : ℤ_[p]) ^ u ∣ Ξ u n j - T (u - 1) (cry p 1 n j 0) (n / p) (j / p)
  Ttow : ∀ u, 1 ≤ u → ∀ δ, δ < 2 → ∀ q q',
      (p : ℤ_[p]) ^ u ∣ T u δ q q' - T (u - 1) (cry p 1 q q' δ) (q / p) (q' / p)

section aux

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
lemma geom_inv {R : Type*} [CommRing R] (x y c l : R) (hx : l * x = 1) (hy : (c + l) * y = 1)
    (T : ℕ) : y - ∑ t ∈ range T, (-c) ^ t * x ^ (t + 1) = (-c) ^ T * x ^ T * y := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    have e : y - x = -c * x * y := by linear_combination x * hy - y * hx
    linear_combination ((-c) ^ T * x ^ T) * e

lemma S_one (n : ℕ) : S p 1 n = H p n := by
  unfold S H; simp only [pow_one]

lemma H_zero : H p 0 = 0 := by
  unfold H; simp

/-- `H′_{c+n} - H′_c = Σ_{t<T} (-c)^t S_{t+1}(n) + c^T (…)` for `p ∣ c` (the truncated
geometric expansion of `1/(c+λ)` used for `X̂₃`, `X_{s,3}` in §4). -/
lemma H_expand (c n T : ℕ) (hc : p ∣ c) :
    (c : ℤ_[p]) ^ T ∣ H p (c + n) - H p c
      - ∑ t ∈ range T, (-(c : ℤ_[p])) ^ t * S p (t + 1) n := by
  have hS : ∀ t, S p (t + 1) n
      = ∑ i ∈ range n, Ring.inverse (((i + 1 : ℕ)) : ℤ_[p]) ^ (t + 1) := by
    intro t
    unfold S
    rw [Finset.sum_range_succ']
    simp
  rw [H_add p c n]
  simp only [hS]
  have e : H p c + ∑ i ∈ range n, Ring.inverse (((c + (i + 1) : ℕ)) : ℤ_[p]) - H p c
      - ∑ t ∈ range T, (-(c : ℤ_[p])) ^ t
          * ∑ i ∈ range n, Ring.inverse (((i + 1 : ℕ)) : ℤ_[p]) ^ (t + 1)
      = ∑ i ∈ range n, (Ring.inverse (((c + (i + 1) : ℕ)) : ℤ_[p])
          - ∑ t ∈ range T, (-(c : ℤ_[p])) ^ t * Ring.inverse (((i + 1 : ℕ)) : ℤ_[p]) ^ (t + 1)) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := range T)]
    ring
  rw [e]
  apply Finset.dvd_sum
  intro i _
  by_cases hi : p ∣ i + 1
  · rw [inv_eq_zero_of_dvd p (dvd_add hc hi), inv_eq_zero_of_dvd p hi]
    simp
  · set x := Ring.inverse (((i + 1 : ℕ)) : ℤ_[p]) with hxdef
    set y := Ring.inverse (((c + (i + 1) : ℕ)) : ℤ_[p]) with hydef
    have hx : (((i + 1 : ℕ)) : ℤ_[p]) * x = 1 := mul_inv_nat p hi
    have hy : (((c + (i + 1) : ℕ)) : ℤ_[p]) * y = 1 := mul_inv_nat p (not_dvd_add p hc hi)
    rw [Nat.cast_add c (i + 1)] at hy
    rw [geom_inv x y (c : ℤ_[p]) _ hx hy T]
    have hc' : (c : ℤ_[p]) ^ T ∣ (-(c : ℤ_[p])) ^ T := by
      rw [neg_pow]; exact dvd_mul_left _ _
    exact (hc'.mul_right _).mul_right _

end aux

namespace KerData

variable {p : ℕ} [Fact p.Prime] {m : ℕ} (D : KerData p m)

lemma tow (w n j : ℕ) : (p : ℤ_[p]) ^ (w + 1) ∣ D.Ψ (w + 1) n (p * j) - D.Ψ w (n / p) j := by
  have h := D.fo w n j
  have hL : (p : ℤ_[p]) ^ (w + 1) ∣ ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) := ppow_dvd_cast p m (w + 1)
  have h1 : (p : ℤ_[p]) ^ (w + 1) ∣ (p : ℤ_[p]) ^ (2 * w + 2) := pow_dvd_pow _ (by omega)
  have e : D.Ψ (w + 1) n (p * j) - D.Ψ w (n / p) j
      = (D.Ψ (w + 1) n (p * j) - D.Ψ w (n / p) j * (1 - ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
          * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))))
        - ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * (D.Ψ w (n / p) j
          * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))) := by ring
  rw [e]
  exact _root_.dvd_sub (h1.trans h) (hL.mul_right _)

lemma unsc_dvd (u n j : ℕ) (hj : ¬ p ∣ j) : (p : ℤ_[p]) ^ u ∣ D.Ψ u n j := by
  rw [D.unsc u n j hj, mul_assoc]
  exact (ppow_dvd_cast p m u).mul_right _

/-- Weighted kernel `Σ_{j < L_u} Ψ_u(q,j) g(j)`. -/
noncomputable def Kg (u q : ℕ) (g : ℕ → ℤ_[p]) : ℤ_[p] :=
  ∑ j ∈ range (m * p ^ u), D.Ψ u q j * g j

/-- `K̂_{w+1}(n) = Σ_{j₁ < L_w} Ψ_{w+1}(n, p j₁)` (scaled kernel indices only). -/
noncomputable def Khat (w n : ℕ) : ℤ_[p] := ∑ j ∈ range (m * p ^ w), D.Ψ (w + 1) n (p * j)

/-- `A(s, σ) = Σ_{q < L_s} σ_σ(q) K_s(q)`. -/
noncomputable def A (s σ : ℕ) : ℤ_[p] := ∑ q ∈ range (m * p ^ s), sig p σ q * D.Kg s q (fun _ => 1)

/-- Lemma 3.4(a)/(c)/(d), general weight. -/
lemma Kg_tower (w q : ℕ) (g : ℕ → ℤ_[p]) :
    (p : ℤ_[p]) ^ (w + 1) ∣ D.Kg (w + 1) q g - D.Kg w (q / p) (fun j => g (p * j)) := by
  unfold Kg
  rw [show m * p ^ (w + 1) = p * (m * p ^ w) by ring]
  refine split_tower p (m * p ^ w) (w + 1) (fun j => D.Ψ (w + 1) q j * g j)
    (fun j => D.Ψ w (q / p) j * g (p * j)) (fun j => ?_) (fun j hj => ?_)
  · beta_reduce
    rw [← sub_mul]; exact (D.tow w q j).mul_right _
  · exact (D.unsc_dvd (w + 1) q j hj).mul_right _

lemma Kk_tower (u : ℕ) (hu : 1 ≤ u) (q : ℕ) :
    (p : ℤ_[p]) ^ u ∣ D.Kg u q (fun _ => 1) - D.Kg (u - 1) (q / p) (fun _ => 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact D.Kg_tower w q (fun _ => 1)

/-- Lemma 3.4(c) (moment kernels). -/
lemma Kg_moment (u q t : ℕ) (ht : 1 ≤ t) :
    (p : ℤ_[p]) ^ u ∣ D.Kg u q (fun j => (j : ℤ_[p]) ^ t) := by
  induction u generalizing q with
  | zero => simp
  | succ u ih =>
    have h := D.Kg_tower u q (fun j => (j : ℤ_[p]) ^ t)
    have e : D.Kg u (q / p) (fun j => (((p * j : ℕ)) : ℤ_[p]) ^ t)
        = (p : ℤ_[p]) ^ t * D.Kg u (q / p) (fun j => (j : ℤ_[p]) ^ t) := by
      unfold Kg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [e] at h
    have h2 : (p : ℤ_[p]) ^ (u + 1)
        ∣ (p : ℤ_[p]) ^ t * D.Kg u (q / p) (fun j => (j : ℤ_[p]) ^ t) := by
      rw [show u + 1 = 1 + u by ring, pow_add]
      exact mul_dvd_mul (pow_dvd_pow _ ht) (ih (q / p))
    have := dvd_add h h2
    rwa [sub_add_cancel] at this

/-- Lemma 3.4(d) (harmonically weighted kernels). -/
lemma Kg_har (w q d : ℕ) :
    (p : ℤ_[p]) ^ (w + 1) ∣ D.Kg (w + 1) q (fun j => H p (p ^ d * j))
      - D.Kg w (q / p) (fun j => H p (p ^ (d + 1) * j)) := by
  have h := D.Kg_tower w q (fun j => H p (p ^ d * j))
  have e : (fun j => H p (p ^ d * (p * j))) = (fun j => H p (p ^ (d + 1) * j)) := by
    funext j; rw [show p ^ d * (p * j) = p ^ (d + 1) * j by ring]
  rwa [e] at h

/-- `X₁`-type piece (§4, `X̂₁`, `X_{s,1}`): Lemma 2.5 + Lemma 3.1. -/
lemma X1 (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + w + 1) ∣ ∑ n ∈ range (m * p ^ (w + 1)),
      sig p σ n * H p n * D.Kg w (n / p) (fun _ => 1) := by
  have hF : ∀ k : ℕ, (fun n => sig p σ n * H p n) k = 0 ∨ (p : ℤ_[p]) ^ (w + 1) ∣
      (fun n => D.Kg w (n / p) (fun _ => 1)) k
        - (fun u q => D.Kg u q (fun _ => 1)) (w + 1 - 1) (k / p) := by
    intro k; right; simp
  have h := block_ind_top_range p (fun u q => D.Kg u q (fun _ => 1)) (w + 1) (2 * σ)
    (fun u hu1 _ k => D.Kk_tower u hu1 k)
    (fun n => D.Kg w (n / p) (fun _ => 1)) (fun n => sig p σ n * H p n)
    hF (fun t _ l => dh1 p hp5 σ t l) m
  rw [show w + 1 + 2 * σ = 2 * σ + w + 1 by ring] at h
  exact h

/-- `X₂`-type piece (§4, `X̂₂`, `X_{s,2}`): Lemma 2.2 + Lemma 3.1 with the tower of 3.4(d). -/
lemma X2 (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + w + 1) ∣ ∑ n ∈ range (m * p ^ (w + 1)),
      sig p σ n * D.Kg w (n / p) (fun j => H p (p * j)) := by
  have hT : ∀ u, 1 ≤ u → u < w + 1 → ∀ k, (p : ℤ_[p]) ^ u ∣
      (fun u q => D.Kg u q (fun j => H p (p ^ (w + 1 - u) * j))) u k
        - (fun u q => D.Kg u q (fun j => H p (p ^ (w + 1 - u) * j))) (u - 1) (k / p) := by
    intro u hu1 hu k
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have h := D.Kg_har v k (w + 1 - (v + 1))
    simp only [Nat.add_sub_cancel]
    rw [show w + 1 - v = w + 1 - (v + 1) + 1 by omega]
    exact h
  have hF : ∀ k : ℕ, (fun n => sig p σ n) k = 0 ∨ (p : ℤ_[p]) ^ (w + 1) ∣
      (fun n => D.Kg w (n / p) (fun j => H p (p * j))) k
        - (fun u q => D.Kg u q (fun j => H p (p ^ (w + 1 - u) * j))) (w + 1 - 1) (k / p) := by
    intro k; right
    simp only [Nat.add_sub_cancel, show w + 1 - w = 1 by omega, pow_one, sub_self]
    exact dvd_zero _
  have ha : ∀ t, t ≤ w + 1 → ∀ l, (p : ℤ_[p]) ^ (t + 2 * σ) ∣
      ∑ k ∈ blk p t l, (fun n => sig p σ n) k := by
    intro t _ l
    rw [sig_merge]
    exact (pow_dvd_pow _ (by omega)).trans (sig_dvd p hp5 (σ + t) l)
  have h := block_ind_top_range p (fun u q => D.Kg u q (fun j => H p (p ^ (w + 1 - u) * j)))
    (w + 1) (2 * σ) hT (fun n => D.Kg w (n / p) (fun j => H p (p * j))) (fun n => sig p σ n)
    hF ha m
  rw [show w + 1 + 2 * σ = 2 * σ + w + 1 by ring] at h
  exact h

/-- Per-index expansion of `Σ_j Ψ(q,j) H′_{n+pj}` (for `X₃`). -/
lemma Kg_expand (w q n T : ℕ) :
    (p : ℤ_[p]) ^ T ∣ D.Kg w q (fun j => H p (n + p * j)) - D.Kg w q (fun j => H p (p * j))
      - ∑ t ∈ range T, (-(p : ℤ_[p])) ^ t * S p (t + 1) n * D.Kg w q (fun j => (j : ℤ_[p]) ^ t) := by
  unfold Kg
  have h3 : ∑ t ∈ range T, (-(p : ℤ_[p])) ^ t * S p (t + 1) n
        * ∑ j ∈ range (m * p ^ w), D.Ψ w q j * (j : ℤ_[p]) ^ t
      = ∑ j ∈ range (m * p ^ w), D.Ψ w q j
          * ∑ t ∈ range T, (-((p * j : ℕ) : ℤ_[p])) ^ t * S p (t + 1) n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro t _
    push_cast; ring
  rw [h3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  have e : D.Ψ w q j * H p (n + p * j) - D.Ψ w q j * H p (p * j)
      - D.Ψ w q j * ∑ t ∈ range T, (-((p * j : ℕ) : ℤ_[p])) ^ t * S p (t + 1) n
      = D.Ψ w q j * (H p (p * j + n) - H p (p * j)
          - ∑ t ∈ range T, (-((p * j : ℕ) : ℤ_[p])) ^ t * S p (t + 1) n) := by
    rw [Nat.add_comm (p * j) n]; ring
  rw [e]
  apply Dvd.dvd.mul_left
  have h := H_expand p (p * j) n T (dvd_mul_right p j)
  have hd : (p : ℤ_[p]) ^ T ∣ ((p * j : ℕ) : ℤ_[p]) ^ T :=
    pow_dvd_pow_of_dvd ⟨(j : ℤ_[p]), by push_cast; ring⟩ T
  exact hd.trans h

/-- `X₃`-type piece (§4, `X̂₃`, `X_{s,3}`): expansion + moment kernels. -/
lemma X3 (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + w + 1) ∣ ∑ n ∈ range (m * p ^ (w + 1)),
      sig p σ n * D.Kg w (n / p) (fun j => H p (n + p * j)) := by
  have hsplit : ∀ n, sig p σ n * D.Kg w (n / p) (fun j => H p (n + p * j))
      = sig p σ n * (D.Kg w (n / p) (fun j => H p (n + p * j)) - D.Kg w (n / p) (fun j => H p (p * j))
          - ∑ t ∈ range (2 * σ + w + 1), (-(p : ℤ_[p])) ^ t * S p (t + 1) n
              * D.Kg w (n / p) (fun j => (j : ℤ_[p]) ^ t))
        + sig p σ n * D.Kg w (n / p) (fun j => H p (p * j))
        + sig p σ n * H p n * D.Kg w (n / p) (fun _ => 1)
        + sig p σ n * ∑ t ∈ range (2 * σ + w), (-(p : ℤ_[p])) ^ (t + 1) * S p (t + 1 + 1) n
            * D.Kg w (n / p) (fun j => (j : ℤ_[p]) ^ (t + 1)) := by
    intro n
    have h0 : ∑ t ∈ range (2 * σ + w + 1), (-(p : ℤ_[p])) ^ t * S p (t + 1) n
          * D.Kg w (n / p) (fun j => (j : ℤ_[p]) ^ t)
        = ∑ t ∈ range (2 * σ + w), (-(p : ℤ_[p])) ^ (t + 1) * S p (t + 1 + 1) n
            * D.Kg w (n / p) (fun j => (j : ℤ_[p]) ^ (t + 1))
          + H p n * D.Kg w (n / p) (fun _ => 1) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, zero_add, S_one]
    rw [h0]
    ring
  rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
  simp only [Finset.sum_add_distrib]
  refine dvd_add (dvd_add (dvd_add ?_ (D.X2 hp5 w σ)) (D.X1 hp5 w σ)) ?_
  · apply Finset.dvd_sum; intro n _
    exact (D.Kg_expand w (n / p) n (2 * σ + w + 1)).mul_left _
  · apply Finset.dvd_sum; intro n _
    have hs := sig_dvd p hp5 σ n
    have hsum : (p : ℤ_[p]) ^ (w + 1) ∣ ∑ t ∈ range (2 * σ + w), (-(p : ℤ_[p])) ^ (t + 1)
        * S p (t + 1 + 1) n * D.Kg w (n / p) (fun j => (j : ℤ_[p]) ^ (t + 1)) := by
      apply Finset.dvd_sum; intro t _
      have h1 : (p : ℤ_[p]) ∣ (-(p : ℤ_[p])) ^ (t + 1) := dvd_pow (dvd_neg.mpr dvd_rfl) (by omega)
      have h2 := D.Kg_moment w (n / p) (t + 1) (by omega)
      rw [show w + 1 = 1 + w by ring, pow_add, pow_one]
      exact mul_dvd_mul (h1.mul_right _) h2
    rw [show 2 * σ + w + 1 = 2 * σ + (w + 1) by ring, pow_add]
    exact mul_dvd_mul hs hsum

/-- `X̂`, `X_s` of §4: `Σ_n σ_σ(n) Σ_j Ψ_w([n/p], j) ρ(n, j) ≡ 0 (mod p^(2σ+w+1))`. -/
lemma Xs (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + w + 1) ∣ ∑ n ∈ range (m * p ^ (w + 1)), sig p σ n *
      ∑ j ∈ range (m * p ^ w), D.Ψ w (n / p) j
        * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j)) := by
  have e : ∀ n, sig p σ n * ∑ j ∈ range (m * p ^ w), D.Ψ w (n / p) j
        * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))
      = D.c₁ * (sig p σ n * H p n * D.Kg w (n / p) (fun _ => 1))
        + D.c₂ * (sig p σ n * D.Kg w (n / p) (fun j => H p (p * j)))
        + D.c₃ * (sig p σ n * D.Kg w (n / p) (fun j => H p (n + p * j))) := by
    intro n
    unfold Kg
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl (fun n _ => e n), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  exact dvd_add (dvd_add ((D.X1 hp5 w σ).mul_left _) ((D.X2 hp5 w σ).mul_left _))
    ((D.X3 hp5 w σ).mul_left _)

/-- `Y_s` of §4: Lemma 3.2 at level `w+1` with Lemma 2.7(Y). -/
lemma Ystep (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + w + 1) ∣ ∑ n ∈ range (m * p ^ (w + 1)), ∑ j ∈ range (m * p ^ (w + 1)),
      sig p σ n * Ring.inverse (j : ℤ_[p]) * D.Ξ (w + 1) n j := by
  have hF : ∀ q q' : ℕ, (fun n j => sig p σ n * Ring.inverse (j : ℤ_[p])) q q' = 0 ∨
      (p : ℤ_[p]) ^ (w + 1) ∣ (fun n j => D.Ξ (w + 1) n j) q q'
        - D.T (w + 1 - 1) (cry p 1 q q' 0) (q / p) (q' / p) := by
    intro q q'
    by_cases hq' : p ∣ q'
    · left; simp [inv_eq_zero_of_dvd p hq']
    · right; exact D.Ξtow (w + 1) q q' (by omega) hq'
  have h := block_ind2_top_range p D.T (w + 1) (2 * σ)
    (fun u hu1 _ δ hδ q q' => D.Ttow u hu1 δ hδ q q')
    (fun n j => D.Ξ (w + 1) n j) (fun n j => sig p σ n * Ring.inverse (j : ℤ_[p]))
    hF (fun t _ i i' c => carry_Y p hp5 σ t i i' c) m m
  rw [show w + 1 + 2 * σ = 2 * σ + w + 1 by ring] at h
  exact h

lemma sum_sig_div (σ w : ℕ) (f : ℕ → ℤ_[p]) :
    ∑ n ∈ range (m * p ^ (w + 1)), sig p σ n * f (n / p)
      = ∑ q ∈ range (m * p ^ w), sig p (σ + 1) q * f q := by
  rw [show m * p ^ (w + 1) = m * p ^ w * p ^ 1 by ring, sum_range_blk p 1 (m * p ^ w)]
  apply Finset.sum_congr rfl
  intro q _
  rw [← sig_merge p σ 1 q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [div_of_mem_blk_one p hn]

/-- The step `A_{s+1}`-scaled part `≡ A_s` (§4, (4.b) and the induction step). -/
lemma Khat_step (hp5 : 5 ≤ p) (w σ : ℕ) :
    (p : ℤ_[p]) ^ (2 * σ + 2 * w + 2) ∣
      ∑ n ∈ range (m * p ^ (w + 1)), sig p σ n * D.Khat w n - D.A w (σ + 1) := by
  have hA : D.A w (σ + 1)
      = ∑ n ∈ range (m * p ^ (w + 1)), sig p σ n * D.Kg w (n / p) (fun _ => 1) := by
    unfold A; exact (sum_sig_div σ w (fun q => D.Kg w q (fun _ => 1))).symm
  have hn : ∀ n, sig p σ n * D.Khat w n - sig p σ n * D.Kg w (n / p) (fun _ => 1)
      = sig p σ n * ∑ j ∈ range (m * p ^ w), (D.Ψ (w + 1) n (p * j) - D.Ψ w (n / p) j
          * (1 - ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
            * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))))
        - ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * (sig p σ n * ∑ j ∈ range (m * p ^ w), D.Ψ w (n / p) j
          * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))) := by
    intro n
    have hj : ∑ j ∈ range (m * p ^ w), (D.Ψ (w + 1) n (p * j) - D.Ψ w (n / p) j
          * (1 - ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
            * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j))))
        = D.Khat w n - D.Kg w (n / p) (fun _ => 1) + ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
          * ∑ j ∈ range (m * p ^ w), D.Ψ w (n / p) j
            * (D.c₁ * H p n + D.c₂ * H p (p * j) + D.c₃ * H p (n + p * j)) := by
      unfold Khat Kg
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hj]
    ring
  rw [hA, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun n _ => hn n), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  apply _root_.dvd_sub
  · apply Finset.dvd_sum; intro n _
    rw [show 2 * σ + 2 * w + 2 = 2 * σ + (2 * w + 2) by ring, pow_add]
    exact mul_dvd_mul (sig_dvd p hp5 σ n) (Finset.dvd_sum fun j _ => D.fo w n j)
  · rw [show 2 * σ + 2 * w + 2 = (w + 1) + (2 * σ + w + 1) by ring, pow_add]
    exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) (D.Xs hp5 w σ)

/-- Splitting `K_{w+1}(n)` into scaled (`K̂`) and unscaled (`L Σ j⁻¹ Ξ`) kernel indices. -/
lemma Kk_split (w n : ℕ) :
    D.Kg (w + 1) n (fun _ => 1) = D.Khat w n + ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) *
      ∑ j ∈ range (m * p ^ (w + 1)), Ring.inverse (j : ℤ_[p]) * D.Ξ (w + 1) n j := by
  unfold Kg Khat
  have h1 : ∑ j ∈ range (m * p ^ (w + 1)), D.Ψ (w + 1) n j * 1
      = ∑ j ∈ range (m * p ^ w), D.Ψ (w + 1) n (p * j) * 1
        + ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j), D.Ψ (w + 1) n j * 1 := by
    rw [show m * p ^ (w + 1) = p * (m * p ^ w) by ring]
    exact sum_range_mul_split p _ _
  have h2 : ∑ j ∈ (range (m * p ^ (w + 1))).filter (fun j => ¬ p ∣ j), D.Ψ (w + 1) n j * 1
      = ∑ j ∈ range (m * p ^ (w + 1)), ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
          * (Ring.inverse (j : ℤ_[p]) * D.Ξ (w + 1) n j) := by
    rw [← sum_filter_ndvd p (range (m * p ^ (w + 1))) _
      (fun j hj => by rw [inv_eq_zero_of_dvd p hj]; ring)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [D.unsc (w + 1) n j (Finset.mem_filter.mp hj).2]
    ring
  rw [h1, h2, Finset.mul_sum]
  simp only [mul_one]

/-- **Induction of §4**: `p^(2σ+2s) ∣ A(s, σ)`; in particular `A_{r-1} = A(r-1, 1) ≡ 0 (mod p^(2r))`. -/
theorem A_dvd (hp5 : 5 ≤ p) (s σ : ℕ) : (p : ℤ_[p]) ^ (2 * σ + 2 * s) ∣ D.A s σ := by
  induction s generalizing σ with
  | zero =>
    unfold A
    apply Finset.dvd_sum
    intro q _
    rw [mul_zero, add_zero]
    exact (sig_dvd p hp5 σ q).mul_right _
  | succ w ih =>
    have e1 : D.A (w + 1) σ = ∑ n ∈ range (m * p ^ (w + 1)), sig p σ n * D.Khat w n
        + ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * ∑ n ∈ range (m * p ^ (w + 1)),
            ∑ j ∈ range (m * p ^ (w + 1)), sig p σ n * Ring.inverse (j : ℤ_[p]) * D.Ξ (w + 1) n j := by
      unfold A
      simp only [D.Kk_split, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e1]
    apply dvd_add
    · rw [← sub_add_cancel (∑ n ∈ range (m * p ^ (w + 1)), sig p σ n * D.Khat w n) (D.A w (σ + 1))]
      apply dvd_add
      · rw [show 2 * σ + 2 * (w + 1) = 2 * σ + 2 * w + 2 by ring]
        exact D.Khat_step hp5 w σ
      · rw [show 2 * σ + 2 * (w + 1) = 2 * (σ + 1) + 2 * w by ring]
        exact ih (σ + 1)
    · rw [show 2 * σ + 2 * (w + 1) = (w + 1) + (2 * σ + w + 1) by ring, pow_add]
      exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) (D.Ystep hp5 w σ)

/-- **Top level of §4/§5**: `p^(2r) ∣ Σ_{n < N} (N+n)⁻¹ K̂_r(n)`, `N = m p^r`, `r = w + 1`. -/
theorem top (hp5 : 5 ≤ p) (w : ℕ) :
    (p : ℤ_[p]) ^ (2 * w + 2) ∣ ∑ n ∈ range (m * p ^ (w + 1)),
      Ring.inverse ((m * p ^ (w + 1) + n : ℕ) : ℤ_[p]) * D.Khat w n := by
  have hpN : p ^ (w + 1) ∣ m * p ^ (w + 1) := Dvd.intro_left _ rfl
  -- (4.b): the `1/k` term
  have h1 : (p : ℤ_[p]) ^ (2 * w + 2) ∣
      ∑ n ∈ range (m * p ^ (w + 1)), Ring.inverse (n : ℤ_[p]) * D.Khat w n := by
    have hk := D.Khat_step hp5 w 0
    have ha := D.A_dvd hp5 w 1
    simp only [sig_zero, mul_zero, zero_add] at hk
    have := dvd_add hk (show (p : ℤ_[p]) ^ (2 * w + 2) ∣ D.A w 1 by
      rw [show 2 * w + 2 = 2 * 1 + 2 * w by ring]; exact ha)
    rwa [sub_add_cancel] at this
  -- (4.a): the `1/k²` term
  have h2 : (p : ℤ_[p]) ^ (w + 1) ∣
      ∑ n ∈ range (m * p ^ (w + 1)), Ring.inverse (n : ℤ_[p]) ^ 2 * D.Khat w n := by
    have hF : ∀ k : ℕ, (fun n => Ring.inverse (n : ℤ_[p]) ^ 2) k = 0 ∨ (p : ℤ_[p]) ^ (w + 1) ∣
        (fun n => D.Khat w n) k - (fun u q => D.Kg u q (fun _ => 1)) (w + 1 - 1) (k / p) := by
      intro k; right
      simp only [Nat.add_sub_cancel]
      unfold Khat Kg
      rw [← Finset.sum_sub_distrib]
      exact Finset.dvd_sum fun j _ => by rw [mul_one]; exact D.tow w k j
    have h := block_ind_top_range p (fun u q => D.Kg u q (fun _ => 1)) (w + 1) 0
      (fun u hu1 _ k => D.Kk_tower u hu1 k) (fun n => D.Khat w n)
      (fun n => Ring.inverse (n : ℤ_[p]) ^ 2) hF
      (fun t _ l => by rw [add_zero]; exact invsq_blk p hp5 t l) m
    rw [add_zero] at h
    exact h
  have e : ∑ n ∈ range (m * p ^ (w + 1)),
        Ring.inverse ((m * p ^ (w + 1) + n : ℕ) : ℤ_[p]) * D.Khat w n
      = ∑ n ∈ range (m * p ^ (w + 1)), (Ring.inverse ((m * p ^ (w + 1) + n : ℕ) : ℤ_[p])
            - Ring.inverse (n : ℤ_[p])
            + ((m * p ^ (w + 1) : ℕ) : ℤ_[p]) * Ring.inverse (n : ℤ_[p]) ^ 2) * D.Khat w n
        + ∑ n ∈ range (m * p ^ (w + 1)), Ring.inverse (n : ℤ_[p]) * D.Khat w n
        - ((m * p ^ (w + 1) : ℕ) : ℤ_[p])
          * ∑ n ∈ range (m * p ^ (w + 1)), Ring.inverse (n : ℤ_[p]) ^ 2 * D.Khat w n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [e]
  refine _root_.dvd_sub (dvd_add (Finset.dvd_sum fun n _ => ?_) h1) ?_
  · have := inv_shift2 p (w + 1) (m * p ^ (w + 1)) n hpN
    rw [show 2 * w + 2 = 2 * (w + 1) by ring]
    exact this.mul_right _
  · rw [show 2 * w + 2 = (w + 1) + (w + 1) by ring, pow_add]
    exact mul_dvd_mul (ppow_dvd_cast p m (w + 1)) h2

end KerData

end A376462Shift
