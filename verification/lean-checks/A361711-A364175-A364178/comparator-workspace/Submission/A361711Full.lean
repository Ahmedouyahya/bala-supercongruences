import Mathlib
import Submission.Old.InvSquares
import Submission.Old.ProductSplit
import Submission.Old.ClosedForm

/-!
# A361711: Bala's supercongruence `a(p^k) ≡ a(p^(k-1)) (mod p^(3k))`, `p ≥ 5` prime

Formalisation of `notes/A361711-proof.md`. Ingredients:
* `BalaProofs.ClosedForm` — Lemma 1 (closed form at odd arguments, via the Zeilberger certificate);
* `BalaProofs.ProductSplit` — Lemma 2 (the product identities, in the form of one splitting lemma);
* `BalaProofs.InvSquares` (and `UnitSquares`, `UnitSquaresCore`) — Lemma 3 (`Σ_U u⁻² ≡ 0`);
* this file — the assembly in `ZMod (p^(3k))`.
-/

open Nat Int Finset BigOperators

/--
A361711: $a(1) = 1$ and $a(n) = \sum_{k = 0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$ for $n \ge 2$.
-/
def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    -- $n-2$ is the upper limit of summation.
    let m : ℕ := N - 2

    -- The sum is over k from 0 to m, which is Finset.range (m + 1).
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

namespace Bala

/-- `A361711 (m+2)` unfolded. -/
theorem A361711_add_two (m : ℕ) :
    A361711 (m+2) = ∑ k ∈ Finset.range (m+1),
      (-1:ℤ)^k * (((m+2).choose k * (m+2).choose k * m.choose k : ℕ) : ℤ) := by
  rfl

/-- `A361711 (m+2)` is `aQ (m+2)`. -/
theorem A361711_eq_aQ (m : ℕ) : (A361711 (m+2) : ℚ) = aQ (m+2) := by
  rw [A361711_add_two, aQ_add_two']
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [F_add_two]
  ring

/-- the closed form as a product: for `M = 2n+1`, `A361711 M = ∏_{i=1}^{n} (1 - (M/i)^2)`. -/
theorem A361711_odd_prod (M n : ℕ) (hM : M = 2 * n + 1) :
    (A361711 M : ℚ) = ∏ i ∈ Finset.Icc 1 n, (1 - ((M:ℚ) / (i:ℚ))^2) := by
  subst hM
  have hcl : (A361711 (2*n+1) : ℚ) = bO n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [A361711, bO]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h := aQ_odd (m+1)
      rw [show 2*(m+1)+1 = (2*m+1)+2 by ring] at h ⊢
      rw [A361711_eq_aQ]
      exact h
  rw [hcl]
  unfold bO
  simp only [prod_Icc_one_eq_prod_range]
  have h1 := prod_one_sub_eq_choose n
  have h2 := prod_one_add_eq_choose n
  have h3 : ∀ i ∈ Finset.range n,
      (1 - (((2 * n + 1 : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ))^2)
        = (1 - ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1))
          * (1 + ((2 * n + 1 : ℕ) : ℚ) / ((i : ℚ) + 1)) := by
    intro i _
    push_cast
    ring
  rw [Finset.prod_congr rfl h3, Finset.prod_mul_distrib, h1, h2]
  ring

/-- `∏ (1 - ε u) = 1 - Σ ε u` when all pairwise products of the `ε` vanish. -/
theorem prod_one_sub_eq_one_sub_sum {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ε : ι → R) (h : ∀ u ∈ s, ∀ v ∈ s, ε u * ε v = 0) :
    ∏ u ∈ s, (1 - ε u) = 1 - ∑ u ∈ s, ε u := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih (fun u hu v hv => h u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv))]
    have h0 : ε a * ∑ u ∈ s, ε u = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero
        (fun u hu => h a (Finset.mem_insert_self a s) u (Finset.mem_insert_of_mem hu))
    linear_combination h0

end Bala

open Bala in
/--
A361711 Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.
-/
theorem A361711_conjecture_full (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  have hk1 : 1 ≤ k := hk
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hM'odd : Odd (p ^ (k - 1)) := hpodd.pow
  have hModd : Odd (p ^ k) := hpodd.pow
  obtain ⟨n, hn⟩ := hModd
  obtain ⟨n', hn'⟩ := hM'odd
  have hMM' : p ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hnn' : (p ^ k - 1) / 2 = n := by omega
  set U := (Finset.Icc 1 n).filter (fun u => ¬ p ∣ u) with hU
  -- Step 1: the rational identity (★)
  have key : (A361711 (p ^ k) : ℚ)
      = (∏ u ∈ U, (1 - (((p ^ k : ℕ) : ℚ) / (u:ℚ))^2)) * (A361711 (p ^ (k - 1)) : ℚ) := by
    rw [A361711_odd_prod (p ^ k) n hn, A361711_odd_prod (p ^ (k - 1)) n' hn']
    have hsplit : ∏ i ∈ Finset.Icc 1 n, (1 - (((p * p ^ (k - 1) : ℕ) : ℚ) / (i:ℚ)) ^ 2)
        = (∏ u ∈ (Finset.Icc 1 n).filter (fun u => ¬ p ∣ u),
            (1 - (((p * p ^ (k - 1) : ℕ) : ℚ) / (u:ℚ)) ^ 2))
          * ∏ i ∈ Finset.Icc 1 n', (1 - (((p ^ (k - 1) : ℕ) : ℚ) / (i:ℚ)) ^ 2) :=
      prod_split p (p ^ (k - 1)) n n' hpodd hn' (by rw [← hMM']; exact hn) (fun x => 1 - x ^ 2)
    rw [← hMM'] at hsplit
    exact hsplit
  -- Step 2: clear denominators
  have hUpos : ∀ u ∈ U, (u:ℚ) ≠ 0 := by
    intro u hu
    simp only [hU, Finset.mem_filter, Finset.mem_Icc] at hu
    exact_mod_cast (by omega : u ≠ 0)
  have key2 : ((∏ u ∈ U, u ^ 2 : ℕ) : ℤ) * A361711 (p ^ k)
      = A361711 (p ^ (k - 1)) * ∏ u ∈ U, ((u:ℤ) ^ 2 - ((p ^ k : ℕ) : ℤ) ^ 2) := by
    have h : ((∏ u ∈ U, u ^ 2 : ℕ) : ℚ) * (A361711 (p ^ k) : ℚ)
        = (A361711 (p ^ (k - 1)) : ℚ) * ∏ u ∈ U, ((u:ℚ) ^ 2 - ((p ^ k : ℕ) : ℚ) ^ 2) := by
      rw [key]
      have h' : ∀ u ∈ U, (1 - (((p ^ k : ℕ) : ℚ) / (u:ℚ))^2)
          = ((u:ℚ) ^ 2 - ((p ^ k : ℕ) : ℚ) ^ 2) / (u:ℚ) ^ 2 := by
        intro u hu
        have := hUpos u hu
        field_simp
      rw [Finset.prod_congr rfl h', Finset.prod_div_distrib]
      push_cast
      have hD : ∏ u ∈ U, (u:ℚ) ^ 2 ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun u hu => pow_ne_zero 2 (hUpos u hu))
      field_simp
    have h' : ((((∏ u ∈ U, u ^ 2 : ℕ) : ℤ) * A361711 (p ^ k) : ℤ) : ℚ)
        = ((A361711 (p ^ (k - 1)) * ∏ u ∈ U, ((u:ℤ) ^ 2 - ((p ^ k : ℕ) : ℤ) ^ 2) : ℤ) : ℚ) := by
      push_cast at h ⊢
      linear_combination h
    exact Int.cast_injective h'
  -- Step 3: pass to `ZMod (p^(3k))`
  rw [← ZMod.intCast_eq_intCast_iff]
  have : NeZero (p ^ (3 * k)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcopU : ∀ u ∈ U, Nat.Coprime u p := by
    intro u hu
    simp only [hU, Finset.mem_filter, Finset.mem_Icc] at hu
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu.2).symm
  have hinv : ∀ u ∈ U, ∃ w : ℤ, (u:ℤ) * w ≡ 1 [ZMOD ((p ^ (3 * k) : ℕ) : ℤ)] := by
    intro u hu
    have hc : Nat.Coprime u (p ^ (3 * k)) := Nat.Coprime.pow_right _ (hcopU u hu)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
    refine ⟨a, ?_⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨b, by linear_combination -hab⟩
  choose! w hw using hinv
  -- Lemma 3 (M2) for the inverses modulo `p^k`
  have hw' : ∀ u ∈ (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun u => ¬ p ∣ u),
      (u:ℤ) * w u ≡ 1 [ZMOD ((p ^ k : ℕ) : ℤ)] := by
    intro u hu
    rw [hnn'] at hu
    exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) (hw u hu)
  have hsum := sum_inv_sq_half_modEq p k hp h_geq_5 hk1 w hw'
  rw [hnn'] at hsum
  have hsum' : ((p ^ (3 * k) : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) ^ 2 * ∑ u ∈ U, (w u) ^ 2 := by
    have h1 := Int.modEq_zero_iff_dvd.mp hsum
    have h2 : ((p ^ (3 * k) : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) ^ 2 * ((p ^ k : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h2]
    exact mul_dvd_mul_left _ h1
  -- cast the integer identity
  have key3 := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * k))) key2
  push_cast at key3
  have hM4 : ((p : ZMod (p ^ (3 * k))) ^ k) ^ 4 = 0 := by
    have h0 : ((p ^ (3 * k) : ℕ) : ZMod (p ^ (3 * k))) = 0 := ZMod.natCast_self _
    push_cast at h0
    calc ((p : ZMod (p ^ (3 * k))) ^ k) ^ 4
        = (p : ZMod (p ^ (3 * k))) ^ (3 * k) * (p : ZMod (p ^ (3 * k))) ^ k := by ring
      _ = 0 := by rw [h0, zero_mul]
  have hprod : ∏ u ∈ U, ((u : ZMod (p ^ (3 * k))) ^ 2 - ((p : ZMod (p ^ (3 * k))) ^ k) ^ 2)
      = ∏ u ∈ U, (u : ZMod (p ^ (3 * k))) ^ 2 := by
    have hstep : ∀ u ∈ U, (u : ZMod (p ^ (3 * k))) ^ 2 - ((p : ZMod (p ^ (3 * k))) ^ k) ^ 2
        = (u : ZMod (p ^ (3 * k))) ^ 2
          * (1 - ((p : ZMod (p ^ (3 * k))) ^ k) ^ 2 * ((w u : ℤ) : ZMod (p ^ (3 * k))) ^ 2) := by
      intro u hu
      have h1 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hw u hu)
      push_cast at h1
      linear_combination (((p : ZMod (p ^ (3 * k))) ^ k) ^ 2
        * ((u : ZMod (p ^ (3 * k))) * ((w u : ℤ) : ZMod (p ^ (3 * k))) + 1)) * h1
    rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, prod_one_sub_eq_one_sub_sum]
    · rw [← Finset.mul_sum]
      have hz : ((p : ZMod (p ^ (3 * k))) ^ k) ^ 2
          * ∑ u ∈ U, ((w u : ℤ) : ZMod (p ^ (3 * k))) ^ 2 = 0 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hsum'
        push_cast at this
        exact this
      rw [hz, sub_zero, mul_one]
    · intro u _ v _
      linear_combination (((w u : ℤ) : ZMod (p ^ (3 * k))) ^ 2
        * ((w v : ℤ) : ZMod (p ^ (3 * k))) ^ 2) * hM4
  rw [hprod] at key3
  have hDunit : IsUnit (∏ u ∈ U, (u : ZMod (p ^ (3 * k))) ^ 2) := by
    have hc : Nat.Coprime (∏ u ∈ U, u ^ 2) (p ^ (3 * k)) := by
      apply Nat.Coprime.prod_left
      intro u hu
      exact Nat.Coprime.pow _ _ (hcopU u hu)
    have := (ZMod.isUnit_iff_coprime _ _).mpr hc
    push_cast at this
    exact this
  exact hDunit.mul_left_cancel (by rw [key3]; ring)
