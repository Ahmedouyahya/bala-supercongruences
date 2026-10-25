import Submission.A386548Padic

/-!
# Osburn–Sahu–Straub machinery (sequence-independent part)

Shared lemmas for the OSS-type supercongruence proofs (`proofs/A363983.md`, Lemmas 1–4 and 6),
built on Epoch AI's accepted Lean proof of A361883 (`BalaCheck/EpochJac.lean`, namespace
`Epoch361883`) and on `BalaCheck/A386548Padic.lean`.

* Lemma 1 (Kazandzidis, strong form, any `A B`): `kaz_padic`, `kaz_int`.
* Lemma 3 (`(-1)^k C(m p^r - 1, k)`): `lemma3_padic`, `lemma3_int`, index `k - 1`: `lemma3_pred_int`.
* Lemma 4 (i), (ii): `lemma4i_int`, `lemma4i_pred_int`, `lemma4ii_int` (and `ℤ_[p]` forms).
* Lemma 2 (half blocks of inverse squares): `half_lower`, `half_upper`, `block_sum`.
* Lemma 6 (level induction, abstract kernel): `level_sum`, `level_sum_weight`, `level_sum_zmod`.
-/

open Nat Finset

namespace OSS

section general

variable (p : ℕ) [Fact p.Prime]

/- ### Valuation helpers -/

lemma fact_min_le_sub (x y : ℕ) (hyx : y < x) :
    min (x.factorization p) (y.factorization p) ≤ (x - y).factorization p := by
  have hp : p.Prime := Fact.out
  set e := min (x.factorization p) (y.factorization p)
  have h1 : p ^ e ∣ x := (pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd x p)
  have h2 : p ^ e ∣ y := (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd y p)
  have h3 : p ^ e ∣ x - y := Nat.dvd_sub h1 h2
  exact (hp.pow_dvd_iff_le_factorization (by omega)).mp h3

lemma fact_min_le_add (x y : ℕ) (hxy : x + y ≠ 0) :
    min (x.factorization p) (y.factorization p) ≤ (x + y).factorization p := by
  have hp : p.Prime := Fact.out
  set e := min (x.factorization p) (y.factorization p)
  have h1 : p ^ e ∣ x := (pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd x p)
  have h2 : p ^ e ∣ y := (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd y p)
  exact (hp.pow_dvd_iff_le_factorization hxy).mp (dvd_add h1 h2)

/- ### Lemma 1: Kazandzidis -/

lemma kaz_padic (hp5 : 5 ≤ p) (A B : ℕ) :
    (p : ℤ_[p]) ^ ((A.choose B).factorization p + 3 + A.factorization p + B.factorization p
        + (A - B).factorization p) ∣
      (((p * A).choose (p * B) : ℕ) : ℤ_[p]) - ((A.choose B : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  rcases Nat.lt_or_ge A B with hAB | hBA
  · have h1 : A.choose B = 0 := Nat.choose_eq_zero_of_lt hAB
    have h2 : (p * A).choose (p * B) = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hAB hp0)
    simp [h1, h2]
  rcases Nat.eq_zero_or_pos B with hB0 | hB1
  · subst hB0; simp
  rcases eq_or_lt_of_le hBA with hEq | hlt
  · subst hEq; simp
  obtain ⟨c, rfl⟩ : ∃ c, A = c + B := ⟨A - B, by omega⟩
  have hc1 : 1 ≤ c := by omega
  have hcB : c + B - B = c := by omega
  rw [hcB]
  rcases le_total B c with hle | hle
  · exact Epoch361883.JAC_bound p c B hp5 hB1 hle
  · have h := Epoch361883.JAC_bound p B c hp5 hc1 hle
    have e1 : (c + B).choose B = (B + c).choose c := by
      rw [Nat.add_comm c B]; exact Nat.choose_symm_add
    have e2 : (p * (c + B)).choose (p * B) = (p * (B + c)).choose (p * c) := by
      rw [show p * (c + B) = p * B + p * c by ring, show p * (B + c) = p * B + p * c by ring]
      exact Nat.choose_symm_add
    have e3 : (c + B).factorization p = (B + c).factorization p := by rw [Nat.add_comm]
    rw [e1, e2, e3]
    exact (pow_dvd_pow _ (by omega)).trans h

lemma kaz_int (hp5 : 5 ≤ p) (A B : ℕ) :
    (p : ℤ) ^ ((A.choose B).factorization p + 3 + A.factorization p + B.factorization p
        + (A - B).factorization p) ∣
      (((p * A).choose (p * B) : ℕ) : ℤ) - ((A.choose B : ℕ) : ℤ) := by
  rw [A386548.int_dvd_iff_padic_dvd p]
  push_cast
  exact kaz_padic p hp5 A B

/- ### Lemma 3 -/

/-- `C(n,k+1)(k+1) = C(n,k)(n-k)` in `ℤ` (true subtraction; both sides vanish for `k > n`). -/
lemma choose_succ_right_int (n k : ℕ) :
    ((n.choose (k + 1) : ℕ) : ℤ) * ((k : ℤ) + 1) = ((n.choose k : ℕ) : ℤ) * ((n : ℤ) - k) := by
  rcases le_or_gt k n with h | h
  · have h1 := Nat.choose_succ_right_eq n k
    have h2 : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by rw [Nat.cast_sub h]
    rw [← h2]; exact_mod_cast h1
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]; simp

lemma peel_neg (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    ((-1 : ℤ) ^ k * (((p * d - 1).choose k : ℕ) : ℤ))
        * ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else (i : ℤ))
      = ((-1 : ℤ) ^ (k / p) * (((d - 1).choose (k / p) : ℕ) : ℤ))
        * ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else ((i : ℤ) - ((p * d : ℕ) : ℤ))) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hpd1 : 1 ≤ p * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hN : (((p * d : ℕ)) : ℤ) = (p : ℤ) * d := by push_cast; ring
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hc := choose_succ_right_int (p * d - 1) k
    have hpd : (((p * d - 1 : ℕ)) : ℤ) = ((p * d : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_sub hpd1]; simp
    rw [hpd] at hc
    set P := ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else (i : ℤ)) with hP
    set Q := ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else ((i : ℤ) - ((p * d : ℕ) : ℤ))) with hQ
    set C0 := (((p * d - 1).choose k : ℕ) : ℤ) with hC0
    set C1 := (((p * d - 1).choose (k + 1) : ℕ) : ℤ) with hC1
    by_cases hdv : p ∣ (k + 1)
    · simp only [hdv, if_true, mul_one]
      obtain ⟨μ', hμ⟩ := hdv
      have hμpos : 1 ≤ μ' := by
        rcases Nat.eq_zero_or_pos μ' with h | h
        · rw [h] at hμ; omega
        · exact h
      obtain ⟨μ, rfl⟩ : ∃ μ, μ' = μ + 1 := ⟨μ' - 1, by omega⟩
      have hdiv1 : (k + 1) / p = μ + 1 := by rw [hμ]; exact Nat.mul_div_cancel_left _ hp0
      have hdiv0 : k / p = μ := by
        have hk : k = p * μ + (p - 1) := by
          have : p * (μ + 1) = p * μ + p := by ring
          omega
        rw [hk, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega : p - 1 < p), Nat.add_zero]
      rw [hdiv1]
      rw [hdiv0] at ih
      have hcd := choose_succ_right_int (d - 1) μ
      have hd1 : (((d - 1 : ℕ)) : ℤ) = (d : ℤ) - 1 := by rw [Nat.cast_sub hd]; simp
      rw [hd1] at hcd
      set D0 := (((d - 1).choose μ : ℕ) : ℤ) with hD0
      set D1 := (((d - 1).choose (μ + 1) : ℕ) : ℤ) with hD1
      have hk1 : ((k : ℤ) + 1) = (p : ℤ) * ((μ : ℤ) + 1) := by exact_mod_cast hμ
      have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have ha : C1 * ((μ : ℤ) + 1) = C0 * ((d : ℤ) - ((μ : ℤ) + 1)) := by
        apply mul_left_cancel₀ hpne
        linear_combination hc - C1 * hk1 + C0 * hN - C0 * hk1
      have hne : ((μ : ℤ) + 1) ≠ 0 := by positivity
      apply mul_right_cancel₀ hne
      linear_combination (-(-1 : ℤ) ^ k * P) * ha - ((d : ℤ) - ((μ : ℤ) + 1)) * ih
        + ((-1 : ℤ) ^ μ * Q) * hcd
    · simp only [hdv, if_false]
      have hdiv : (k + 1) / p = k / p := by rw [Nat.succ_div]; simp [hdv]
      rw [hdiv]
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination (-(-1 : ℤ) ^ k * P) * hc + ((k : ℤ) + 1 - ((p * d : ℕ) : ℤ)) * ih

lemma lemma3_int (m r k : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ (-1 : ℤ) ^ k * (((m * p ^ r - 1).choose k : ℕ) : ℤ)
      - (-1 : ℤ) ^ (k / p) * (((m * p ^ (r - 1) - 1).choose (k / p) : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hd1 : 1 ≤ m * p ^ r' :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpd : m * p ^ (r' + 1) = p * (m * p ^ r') := by rw [pow_succ]; ring
  rw [hpd]
  have hpeel := peel_neg p (m * p ^ r') hd1 k
  set d := m * p ^ r' with hd
  set P := ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else (i : ℤ)) with hP
  set Q := ∏ i ∈ Icc 1 k, (if p ∣ i then (1 : ℤ) else ((i : ℤ) - ((p * d : ℕ) : ℤ))) with hQ
  have hQP : (p : ℤ) ^ (r' + 1) ∣ Q - P := by
    rw [hQ, hP]
    apply Epoch361883.dvd_prod_sub_prod
    intro i _
    by_cases hi : p ∣ i
    · simp [hi]
    · simp only [hi, if_false]
      have : ((p * d : ℕ) : ℤ) = (p : ℤ) ^ (r' + 1) * m := by rw [hd]; push_cast; ring
      rw [this]; exact ⟨-(m : ℤ), by ring⟩
  have hcop : IsCoprime ((p : ℤ) ^ (r' + 1)) P := by
    apply IsCoprime.pow_left
    rw [hP]
    apply IsCoprime.prod_right
    intro i _
    by_cases hi : p ∣ i
    · simp only [hi, if_true]; exact isCoprime_one_right
    · simp only [hi, if_false]
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi)
  have hmul : (p : ℤ) ^ (r' + 1) ∣ ((-1 : ℤ) ^ k * (((p * d - 1).choose k : ℕ) : ℤ)
      - (-1 : ℤ) ^ (k / p) * (((d - 1).choose (k / p) : ℕ) : ℤ)) * P := by
    have e : ((-1 : ℤ) ^ k * (((p * d - 1).choose k : ℕ) : ℤ)
        - (-1 : ℤ) ^ (k / p) * (((d - 1).choose (k / p) : ℕ) : ℤ)) * P
        = ((-1 : ℤ) ^ (k / p) * (((d - 1).choose (k / p) : ℕ) : ℤ)) * (Q - P) := by
      linear_combination hpeel
    rw [e]; exact hQP.mul_left _
  exact hcop.dvd_of_dvd_mul_right hmul

lemma lemma3_padic (m r k : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ (-1 : ℤ_[p]) ^ k * (((m * p ^ r - 1).choose k : ℕ) : ℤ_[p])
      - (-1 : ℤ_[p]) ^ (k / p) * (((m * p ^ (r - 1) - 1).choose (k / p) : ℕ) : ℤ_[p]) := by
  have h := lemma3_int p m r k hm hr
  rw [A386548.int_dvd_iff_padic_dvd p] at h
  push_cast at h
  exact h

omit [Fact p.Prime] in
lemma pred_div_eq (k : ℕ) (hk : ¬ p ∣ k) : (k - 1) / p = k / p := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero p)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_div]
  simp [hk]

lemma lemma3_pred_int (m r k : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) (hk : ¬ p ∣ k) :
    (p : ℤ) ^ r ∣ (-1 : ℤ) ^ (k - 1) * (((m * p ^ r - 1).choose (k - 1) : ℕ) : ℤ)
      - (-1 : ℤ) ^ (k / p) * (((m * p ^ (r - 1) - 1).choose (k / p) : ℕ) : ℤ) := by
  have h := lemma3_int p m r (k - 1) hm hr
  rwa [pred_div_eq p k hk] at h

/- ### Lemma 4 -/

lemma lemma4i_padic (m r k : ℕ) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ (((m * p ^ r + k).choose k : ℕ) : ℤ_[p])
      - (((m * p ^ (r - 1) + k / p).choose (k / p) : ℕ) : ℤ_[p]) := by
  have h := Epoch361883.scale_descent p m 0 r k (Nat.zero_le _) hr
  simp only [zero_mul, zero_add] at h
  exact h

lemma lemma4i_int (m r k : ℕ) (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ (((m * p ^ r + k).choose k : ℕ) : ℤ)
      - (((m * p ^ (r - 1) + k / p).choose (k / p) : ℕ) : ℤ) := by
  rw [A386548.int_dvd_iff_padic_dvd p]
  push_cast
  exact lemma4i_padic p m r k hr

lemma lemma4i_pred_int (m r k : ℕ) (hr : 1 ≤ r) (hk : ¬ p ∣ k) :
    (p : ℤ) ^ r ∣ (((m * p ^ r + (k - 1)).choose (k - 1) : ℕ) : ℤ)
      - (((m * p ^ (r - 1) + k / p).choose (k / p) : ℕ) : ℤ) := by
  have h := lemma4i_int p m r (k - 1) hr
  rwa [pred_div_eq p k hk] at h

lemma lemma4ii_padic (m r j : ℕ) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ ((j.choose (m * p ^ r) : ℕ) : ℤ_[p])
      - (((j / p).choose (m * p ^ (r - 1)) : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hpr : m * p ^ (r' + 1) = p * (m * p ^ r') := by rw [pow_succ]; ring
  rcases Nat.lt_or_ge j (m * p ^ (r' + 1)) with hj | hj
  · have h1 : j.choose (m * p ^ (r' + 1)) = 0 := Nat.choose_eq_zero_of_lt hj
    have h2 : (j / p).choose (m * p ^ (r' + 1 - 1)) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      rw [Nat.add_sub_cancel, Nat.div_lt_iff_lt_mul hp0]
      calc j < m * p ^ (r' + 1) := hj
        _ = m * p ^ r' * p := by rw [pow_succ]; ring
    rw [h1, h2]; simp
  · obtain ⟨x, rfl⟩ : ∃ x, j = m * p ^ (r' + 1) + x := ⟨j - m * p ^ (r' + 1), by omega⟩
    have h := lemma4i_padic p m (r' + 1) x hr
    have e1 : (m * p ^ (r' + 1) + x).choose (m * p ^ (r' + 1))
        = (m * p ^ (r' + 1) + x).choose x := Nat.choose_symm_add
    have e2 : (m * p ^ (r' + 1) + x) / p = m * p ^ (r' + 1 - 1) + x / p := by
      rw [hpr, Nat.mul_add_div hp0, Nat.add_sub_cancel]
    have e3 : (m * p ^ (r' + 1 - 1) + x / p).choose (m * p ^ (r' + 1 - 1))
        = (m * p ^ (r' + 1 - 1) + x / p).choose (x / p) := Nat.choose_symm_add
    rw [e1, e2, e3]; exact h

lemma lemma4ii_int (m r j : ℕ) (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ ((j.choose (m * p ^ r) : ℕ) : ℤ) - (((j / p).choose (m * p ^ (r - 1)) : ℕ) : ℤ) := by
  rw [A386548.int_dvd_iff_padic_dvd p]
  push_cast
  exact lemma4ii_padic p m r j hr

/- ### Splitting a sum over `range (pM + 1)` by divisibility -/

lemma sum_split_dvd {R : Type*} [AddCommMonoid R] (M : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (p * M + 1), f k
      = ∑ j ∈ range (M + 1), f (p * j) + ∑ k ∈ (range (p * M + 1)).filter (fun k => ¬ p ∣ k), f k := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * M + 1)) (fun k => p ∣ k)]
  congr 1
  have himg : (range (p * M + 1)).filter (fun k => p ∣ k) = (range (M + 1)).image (fun j => p * j) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, ⟨j, rfl⟩⟩
      have h1 : p * j ≤ p * M := by omega
      exact ⟨j, by have := Nat.le_of_mul_le_mul_left h1 hp0; omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have h1 : p * j ≤ p * M := Nat.mul_le_mul_left p (by omega)
      exact ⟨by omega, dvd_mul_right p j⟩
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hp0 hxy

omit [Fact p.Prime] in
lemma filter_range_succ_of_dvd (N : ℕ) (hN : p ∣ N) :
    (range (N + 1)).filter (fun k => ¬ p ∣ k) = (range N).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hk, hpk⟩
    refine ⟨?_, hpk⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact h
    · exact absurd (h ▸ hN) hpk
  · rintro ⟨hk, hpk⟩
    exact ⟨by omega, hpk⟩

/- ### Lemma 2: half blocks of inverse squares -/

/-- If `p^s ∣ a² - b²` for units `a, b` of `ℤ_[p]`, then `p^s ∣ a⁻² - b⁻²`. -/
lemma inv_sq_sub_dvd (s : ℕ) {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b)
    (h : (p : ℤ_[p]) ^ s ∣ a ^ 2 - b ^ 2) :
    (p : ℤ_[p]) ^ s ∣ Ring.inverse a ^ 2 - Ring.inverse b ^ 2 := by
  rw [Ring.inverse_pow, Ring.inverse_pow]
  exact Epoch361883.dvd_inverse_sub_inverse p s (ha.pow 2) (hb.pow 2) h

lemma inv_sq_shift (s n u : ℕ) (hu : ¬ p ∣ u) :
    (p : ℤ_[p]) ^ s ∣ Ring.inverse (((p ^ s * n + u : ℕ) : ℤ_[p])) ^ 2
      - Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  have hnu : ¬ p ∣ (p ^ s * n + u) := by
    intro h
    exact hu ((Nat.dvd_add_right ((dvd_pow_self p (by omega)).mul_right n)).mp h)
  apply inv_sq_sub_dvd p s (Epoch361883.isUnit_nat_of_not_dvd p hnu)
    (Epoch361883.isUnit_nat_of_not_dvd p hu)
  refine ⟨(n : ℤ_[p]) * ((p : ℤ_[p]) ^ s * n + 2 * u), ?_⟩
  push_cast; ring

/-- Lemma 2 at the base block: both half sums of `u⁻²` over `0 < u < p^s`, `p ∤ u`, vanish
mod `p^s` (`p^s` is odd, and `u ↦ p^s - u` swaps the halves). -/
lemma half_core (hp5 : 5 ≤ p) (s : ℕ) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ 2 * u < p ^ s),
        Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2 ∧
    (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < p ^ s),
        Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hqodd : Odd (p ^ s) := (hp.eq_two_or_odd'.resolve_left (by omega)).pow
  obtain ⟨c, hc⟩ := hqodd
  set q := p ^ s with hq
  set f : ℕ → ℤ_[p] := fun u => Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2 with hf
  have hfull : (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ 2 * u < q), f u
      + ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < q), f u := by
    have h0 := Epoch361883.block_Ico_padic p s 0 hp5 hs
    rw [Epoch361883.toZModPow_eq_zero_iff_dvd] at h0
    rw [Nat.zero_add, ← Finset.range_eq_Ico] at h0
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((range q).filter (fun n => ¬ p ∣ n)) (fun u => 2 * u < q) f
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    rw [hsplit]; exact h0
  -- the two halves are swapped by `u ↦ q - u`
  have hpair : ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < q), f u
      = ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ 2 * u < q), f (q - u) := by
    symm
    apply Finset.sum_nbij' (fun u => q - u) (fun u => q - u)
    · intro u hu
      simp only [mem_filter, mem_range] at hu ⊢
      obtain ⟨hu1, hu2, hu3⟩ := hu
      have hu0 : u ≠ 0 := by rintro rfl; exact hu2 (dvd_zero p)
      refine ⟨by omega, ?_, by omega⟩
      intro hd
      apply hu2
      have := Nat.dvd_sub hpq hd
      rwa [Nat.sub_sub_self hu1.le] at this
    · intro u hu
      simp only [mem_filter, mem_range] at hu ⊢
      obtain ⟨hu1, hu2, hu3⟩ := hu
      have hu0 : u ≠ 0 := by rintro rfl; exact hu2 (dvd_zero p)
      refine ⟨by omega, ?_, by omega⟩
      intro hd
      apply hu2
      have := Nat.dvd_sub hpq hd
      rwa [Nat.sub_sub_self hu1.le] at this
    · intro u hu
      simp only [mem_filter, mem_range] at hu
      omega
    · intro u hu
      simp only [mem_filter, mem_range] at hu
      omega
    · intro u _; rfl
  -- termwise `f (q - u) ≡ f u`
  have hdiff : (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ 2 * u < q),
      (f (q - u) - f u) := by
    apply Finset.dvd_sum
    intro u hu
    simp only [mem_filter, mem_range] at hu
    obtain ⟨hu1, hu2, hu3⟩ := hu
    have hqu : ¬ p ∣ (q - u) := by
      intro hd
      apply hu2
      have := Nat.dvd_sub hpq hd
      rwa [Nat.sub_sub_self hu1.le] at this
    apply inv_sq_sub_dvd p s (Epoch361883.isUnit_nat_of_not_dvd p hqu)
      (Epoch361883.isUnit_nat_of_not_dvd p hu2)
    refine ⟨(p : ℤ_[p]) ^ s - 2 * u, ?_⟩
    rw [Nat.cast_sub hu1.le, hq]
    push_cast; ring
  rw [Finset.sum_sub_distrib, ← hpair] at hdiff
  set L := ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ 2 * u < q), f u with hL
  set U := ∑ u ∈ (range q).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < q), f u with hU
  have h2 : (p : ℤ_[p]) ^ s ∣ 2 * L := by
    have := dvd_sub hfull hdiff
    have e : L + U - (U - L) = 2 * L := by ring
    rwa [e] at this
  have h2unit : IsUnit (2 : ℤ_[p]) := by
    have h2 : ¬ p ∣ 2 := by
      intro h; have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h; omega
    have := Epoch361883.isUnit_nat_of_not_dvd p h2
    simpa using this
  have hLd : (p : ℤ_[p]) ^ s ∣ L := (h2unit.dvd_mul_left).mp h2
  refine ⟨hLd, ?_⟩
  have := dvd_add hdiff hLd
  rwa [sub_add_cancel] at this

lemma half_lower (hp5 : 5 ≤ p) (s : ℕ) (hs : 1 ≤ s) (n : ℕ) :
    (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ 2 * u < p ^ s),
      Ring.inverse (((p ^ s * n + u : ℕ) : ℤ_[p])) ^ 2 := by
  have hcore := (half_core p hp5 s hs).1
  have hsh : (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ 2 * u < p ^ s),
      (Ring.inverse (((p ^ s * n + u : ℕ) : ℤ_[p])) ^ 2 - Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2) := by
    apply Finset.dvd_sum
    intro u hu
    exact inv_sq_shift p s n u (Finset.mem_filter.mp hu).2.1
  rw [Finset.sum_sub_distrib] at hsh
  have := dvd_add hsh hcore
  rwa [sub_add_cancel] at this

lemma half_upper (hp5 : 5 ≤ p) (s : ℕ) (hs : 1 ≤ s) (n : ℕ) :
    (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < p ^ s),
      Ring.inverse (((p ^ s * n + u : ℕ) : ℤ_[p])) ^ 2 := by
  have hcore := (half_core p hp5 s hs).2
  have hsh : (p : ℤ_[p]) ^ s ∣ ∑ u ∈ (range (p ^ s)).filter (fun u => ¬ p ∣ u ∧ ¬ 2 * u < p ^ s),
      (Ring.inverse (((p ^ s * n + u : ℕ) : ℤ_[p])) ^ 2 - Ring.inverse ((u : ℕ) : ℤ_[p]) ^ 2) := by
    apply Finset.dvd_sum
    intro u hu
    exact inv_sq_shift p s n u (Finset.mem_filter.mp hu).2.1
  rw [Finset.sum_sub_distrib] at hsh
  have := dvd_add hsh hcore
  rwa [sub_add_cancel] at this

/-- Block lemma: weights `k⁻²`, kernel evaluated at `(⌊k/p^s⌋, ⌊2k/p^s⌋)`. -/
lemma block_sum (hp5 : 5 ≤ p) (s t B : ℕ) (hs : 1 ≤ s) (g : ℕ → ℕ → ℤ_[p])
    (hg : ∀ n j, (p : ℤ_[p]) ^ t ∣ g n j) :
    (p : ℤ_[p]) ^ (s + t) ∣ ∑ k ∈ (range (p ^ s * B)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2 * g (k / p ^ s) (2 * k / p ^ s) := by
  have hp : p.Prime := Fact.out
  have hq0 : 0 < p ^ s := pow_pos hp.pos s
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  rw [Epoch361883.reindex_filter p (p ^ s) B hpq]
  apply Finset.dvd_sum
  intro μ _
  have hval : ∀ σ ∈ (range (p ^ s)).filter (fun n => ¬ p ∣ n),
      Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2
          * g ((p ^ s * μ + σ) / p ^ s) (2 * (p ^ s * μ + σ) / p ^ s)
        = Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2
          * g μ (2 * μ + (if 2 * σ < p ^ s then 0 else 1)) := by
    intro σ hσ
    have hσq : σ < p ^ s := mem_range.mp (mem_filter.mp hσ).1
    have h1 : (p ^ s * μ + σ) / p ^ s = μ := by
      rw [Nat.mul_add_div hq0, Nat.div_eq_of_lt hσq, Nat.add_zero]
    have h2 : 2 * (p ^ s * μ + σ) / p ^ s = 2 * μ + (if 2 * σ < p ^ s then 0 else 1) := by
      rw [show 2 * (p ^ s * μ + σ) = p ^ s * (2 * μ) + 2 * σ by ring, Nat.mul_add_div hq0]
      split_ifs with h
      · rw [Nat.div_eq_of_lt h]
      · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    rw [h1, h2]
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_filter_add_sum_filter_not _ (fun σ => 2 * σ < p ^ s),
    Finset.filter_filter, Finset.filter_filter]
  have e1 : ∑ σ ∈ (range (p ^ s)).filter (fun σ => ¬ p ∣ σ ∧ 2 * σ < p ^ s),
      Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2
          * g μ (2 * μ + (if 2 * σ < p ^ s then 0 else 1))
      = (∑ σ ∈ (range (p ^ s)).filter (fun σ => ¬ p ∣ σ ∧ 2 * σ < p ^ s),
          Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2) * g μ (2 * μ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [if_pos (mem_filter.mp hσ).2.2, Nat.add_zero]
  have e2 : ∑ σ ∈ (range (p ^ s)).filter (fun σ => ¬ p ∣ σ ∧ ¬ 2 * σ < p ^ s),
      Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2
          * g μ (2 * μ + (if 2 * σ < p ^ s then 0 else 1))
      = (∑ σ ∈ (range (p ^ s)).filter (fun σ => ¬ p ∣ σ ∧ ¬ 2 * σ < p ^ s),
          Ring.inverse (((p ^ s * μ + σ : ℕ)) : ℤ_[p]) ^ 2) * g μ (2 * μ + 1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [if_neg (mem_filter.mp hσ).2.2]
  rw [e1, e2, pow_add]
  exact dvd_add (mul_dvd_mul (half_lower p hp5 s hs μ) (hg _ _))
    (mul_dvd_mul (half_upper p hp5 s hs μ) (hg _ _))

/- ### Lemma 6: the level induction with an abstract kernel -/

/-- `Σ_s` of the level induction: `Σ'_{k < L p^r} k⁻² Ψ (r-s) ⌊k/p^s⌋ ⌊2k/p^s⌋`. -/
noncomputable def levelSig (r L : ℕ) (Ψ : ℕ → ℕ → ℕ → ℤ) (s : ℕ) : ℤ_[p] :=
  ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
    Ring.inverse (k : ℤ_[p]) ^ 2 * ((Ψ (r - s) (k / p ^ s) (2 * k / p ^ s) : ℤ) : ℤ_[p])

theorem level_sum (hp5 : 5 ≤ p) (r L : ℕ) (hr : 1 ≤ r) (Ψ : ℕ → ℕ → ℕ → ℤ)
    (hΨ : ∀ t, 1 ≤ t → t < r → ∀ n j, (p : ℤ) ^ t ∣ Ψ t n j - Ψ (t - 1) (n / p) (j / p)) :
    (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2 * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p]) := by
  have hrange : ∀ s, s ≤ r → L * p ^ r = p ^ s * (L * p ^ (r - s)) := by
    intro s hs
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hs]
  have htop : (p : ℤ_[p]) ^ r ∣ levelSig p r L Ψ r := by
    have h := block_sum p hp5 r 0 L hr (fun n j => ((Ψ (r - r) n j : ℤ) : ℤ_[p]))
      (fun n j => by rw [pow_zero]; exact one_dvd _)
    rw [Nat.add_zero, mul_comm (p ^ r) L] at h
    exact h
  have hstep : ∀ s, 1 ≤ s → s < r →
      (p : ℤ_[p]) ^ r ∣ levelSig p r L Ψ s - levelSig p r L Ψ (s + 1) := by
    intro s hs1 hsr
    have h := block_sum p hp5 s (r - s) (L * p ^ (r - s)) hs1
      (fun n j => ((Ψ (r - s) n j - Ψ (r - s - 1) (n / p) (j / p) : ℤ) : ℤ_[p]))
      (fun n j => (A386548.int_dvd_iff_padic_dvd p _ _).mp (hΨ (r - s) (by omega) (by omega) n j))
    rw [← hrange s hsr.le, Nat.add_sub_cancel' hsr.le] at h
    have e : levelSig p r L Ψ s - levelSig p r L Ψ (s + 1)
        = ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * ((Ψ (r - s) (k / p ^ s) (2 * k / p ^ s)
            - Ψ (r - s - 1) (k / p ^ s / p) (2 * k / p ^ s / p) : ℤ) : ℤ_[p]) := by
      unfold levelSig
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [show r - (s + 1) = r - s - 1 by omega, pow_succ p s, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul, Int.cast_sub, mul_sub]
    rw [e]; exact h
  have hall : ∀ i, i < r → (p : ℤ_[p]) ^ r ∣ levelSig p r L Ψ (r - i) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.sub_zero]; exact htop
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep (r - (i + 1)) (by omega) (by omega)
      rw [show r - (i + 1) + 1 = r - i by omega] at h2
      have := dvd_add h2 h1
      rwa [sub_add_cancel] at this
  have h1 := hall (r - 1) (by omega)
  rw [show r - (r - 1) = 1 by omega] at h1
  unfold levelSig at h1
  simp only [pow_one] at h1
  exact h1

theorem level_sum_weight (hp5 : 5 ≤ p) (r L : ℕ) (hr : 1 ≤ r) (Ψ : ℕ → ℕ → ℕ → ℤ)
    (hΨ : ∀ t, 1 ≤ t → t < r → ∀ n j, (p : ℤ) ^ t ∣ Ψ t n j - Ψ (t - 1) (n / p) (j / p))
    (w : ℕ → ℤ_[p]) (hw : ∀ k, ¬ p ∣ k → (p : ℤ_[p]) ^ r ∣ w k - Ring.inverse (k : ℤ_[p]) ^ 2) :
    (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
      w k * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p]) := by
  have h1 := level_sum p hp5 r L hr Ψ hΨ
  have h2 : (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
      (w k - Ring.inverse (k : ℤ_[p]) ^ 2) * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p]) := by
    apply Finset.dvd_sum
    intro k hk
    exact (hw k (mem_filter.mp hk).2).mul_right _
  have e : ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
        w k * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p])
      = ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p])
        + ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
          (w k - Ring.inverse (k : ℤ_[p]) ^ 2) * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ℤ_[p]) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [e]; exact dvd_add h1 h2

theorem level_sum_zmod (hp5 : 5 ≤ p) (r L : ℕ) (hr : 1 ≤ r) (Ψ : ℕ → ℕ → ℕ → ℤ)
    (hΨ : ∀ t, 1 ≤ t → t < r → ∀ n j, (p : ℤ) ^ t ∣ Ψ t n j - Ψ (t - 1) (n / p) (j / p)) :
    ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
      ((k : ZMod (p ^ r))⁻¹) ^ 2 * ((Ψ (r - 1) (k / p) (2 * k / p) : ℤ) : ZMod (p ^ r)) = 0 := by
  have h := level_sum p hp5 r L hr Ψ hΨ
  rw [← Epoch361883.toZModPow_eq_zero_iff_dvd, map_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  have hpk := (mem_filter.mp hk).2
  have hunit : IsUnit (k : ℤ_[p]) := Epoch361883.isUnit_nat_of_not_dvd p hpk
  have huz : IsUnit ((k : ℕ) : ZMod (p ^ r)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hpk).symm.pow_right r
  rw [map_mul, map_pow, Epoch361883.toZModPow_inverse p r hunit, map_natCast, map_intCast,
    Epoch361883.ring_inverse_eq_inv_zmod _ huz]

/- ### Lemma 6, full-block form with an arbitrary weight

Only the vanishing of the block sums of the weight is used: `hw` asks that the sum of `w` over
the `p ∤ k` part of every block `[n p^s, (n+1) p^s)` (`1 ≤ s ≤ r`) be divisible by `p^s`. -/

omit [Fact p.Prime] in
/-- The `p ∤ ·` part of the block `[μ p^s, (μ+1) p^s)`, written as `p^s μ + σ`, `σ < p^s`. -/
lemma block_reindex (s μ : ℕ) (hs : 1 ≤ s) {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ σ ∈ (range (p ^ s)).filter (fun n => ¬ p ∣ n), f (p ^ s * μ + σ)
      = ∑ k ∈ (Ico (μ * p ^ s) ((μ + 1) * p ^ s)).filter (fun k => ¬ p ∣ k), f k := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Ico_eq_sum_range,
    show (μ + 1) * p ^ s - μ * p ^ s = p ^ s by rw [add_mul, one_mul, Nat.add_sub_cancel_left]]
  apply Finset.sum_congr rfl
  intro σ _
  have hpq : p ∣ μ * p ^ s := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) μ
  rw [show p ^ s * μ + σ = μ * p ^ s + σ by ring]
  simp only [Nat.dvd_add_right hpq]

/-- Block lemma for a general weight: `p^s ∣` every block sum of `w`, `p^t ∣ g`. -/
lemma block_sum_w (s t B : ℕ) (hs : 1 ≤ s) (w : ℕ → ℤ_[p])
    (hw : ∀ n, (p : ℤ_[p]) ^ s ∣
      ∑ k ∈ (Ico (n * p ^ s) ((n + 1) * p ^ s)).filter (fun k => ¬ p ∣ k), w k)
    (g : ℕ → ℤ_[p]) (hg : ∀ n, (p : ℤ_[p]) ^ t ∣ g n) :
    (p : ℤ_[p]) ^ (s + t) ∣ ∑ k ∈ (range (p ^ s * B)).filter (fun k => ¬ p ∣ k),
      w k * g (k / p ^ s) := by
  have hp : p.Prime := Fact.out
  have hq0 : 0 < p ^ s := pow_pos hp.pos s
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  rw [Epoch361883.reindex_filter p (p ^ s) B hpq]
  apply Finset.dvd_sum
  intro μ _
  have hval : ∀ σ ∈ (range (p ^ s)).filter (fun n => ¬ p ∣ n),
      w (p ^ s * μ + σ) * g ((p ^ s * μ + σ) / p ^ s) = w (p ^ s * μ + σ) * g μ := by
    intro σ hσ
    have hσq : σ < p ^ s := mem_range.mp (mem_filter.mp hσ).1
    rw [Nat.mul_add_div hq0, Nat.div_eq_of_lt hσq, Nat.add_zero]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, block_reindex p s μ hs w, pow_add]
  exact mul_dvd_mul (hw μ) (hg μ)

/-- `Σ_s` of the weighted level induction: `Σ'_{k < L p^r} w(k) Ψ (r-s) ⌊k/p^s⌋`. -/
noncomputable def levelSigW (r L : ℕ) (w : ℕ → ℤ_[p]) (Ψ : ℕ → ℕ → ℤ) (s : ℕ) : ℤ_[p] :=
  ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
    w k * ((Ψ (r - s) (k / p ^ s) : ℤ) : ℤ_[p])

/-- **Lemma 6, generic weight**: if all block sums of `w` vanish (`hw`) and the kernel is
self-similar (`hΨ`), then `p^r ∣ Σ'_{k < L p^r} w(k) Ψ (r-1) ⌊k/p⌋`. -/
theorem level_sum_blocks (r L : ℕ) (hr : 1 ≤ r) (w : ℕ → ℤ_[p])
    (hw : ∀ s, 1 ≤ s → s ≤ r → ∀ n, (p : ℤ_[p]) ^ s ∣
      ∑ k ∈ (Ico (n * p ^ s) ((n + 1) * p ^ s)).filter (fun k => ¬ p ∣ k), w k)
    (Ψ : ℕ → ℕ → ℤ)
    (hΨ : ∀ t, 1 ≤ t → t ≤ r - 1 → ∀ n, (p : ℤ) ^ t ∣ Ψ t n - Ψ (t - 1) (n / p)) :
    (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
      w k * ((Ψ (r - 1) (k / p) : ℤ) : ℤ_[p]) := by
  have hrange : ∀ s, s ≤ r → L * p ^ r = p ^ s * (L * p ^ (r - s)) := by
    intro s hs
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hs]
  have htop : (p : ℤ_[p]) ^ r ∣ levelSigW p r L w Ψ r := by
    have h := block_sum_w p r 0 L hr w (hw r hr le_rfl) (fun n => ((Ψ (r - r) n : ℤ) : ℤ_[p]))
      (fun n => by rw [pow_zero]; exact one_dvd _)
    rw [Nat.add_zero, mul_comm (p ^ r) L] at h
    exact h
  have hstep : ∀ s, 1 ≤ s → s < r →
      (p : ℤ_[p]) ^ r ∣ levelSigW p r L w Ψ s - levelSigW p r L w Ψ (s + 1) := by
    intro s hs1 hsr
    have h := block_sum_w p s (r - s) (L * p ^ (r - s)) hs1 w (hw s hs1 hsr.le)
      (fun n => ((Ψ (r - s) n - Ψ (r - s - 1) (n / p) : ℤ) : ℤ_[p]))
      (fun n => (A386548.int_dvd_iff_padic_dvd p _ _).mp (hΨ (r - s) (by omega) (by omega) n))
    rw [← hrange s hsr.le, Nat.add_sub_cancel' hsr.le] at h
    have e : levelSigW p r L w Ψ s - levelSigW p r L w Ψ (s + 1)
        = ∑ k ∈ (range (L * p ^ r)).filter (fun k => ¬ p ∣ k),
          w k * ((Ψ (r - s) (k / p ^ s) - Ψ (r - s - 1) (k / p ^ s / p) : ℤ) : ℤ_[p]) := by
      unfold levelSigW
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [show r - (s + 1) = r - s - 1 by omega, pow_succ p s, ← Nat.div_div_eq_div_mul,
        Int.cast_sub, mul_sub]
    rw [e]; exact h
  have hall : ∀ i, i < r → (p : ℤ_[p]) ^ r ∣ levelSigW p r L w Ψ (r - i) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.sub_zero]; exact htop
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep (r - (i + 1)) (by omega) (by omega)
      rw [show r - (i + 1) + 1 = r - i by omega] at h2
      have := dvd_add h2 h1
      rwa [sub_add_cancel] at this
  have h1 := hall (r - 1) (by omega)
  rw [show r - (r - 1) = 1 by omega] at h1
  unfold levelSigW at h1
  simp only [pow_one] at h1
  exact h1

/-- The weight `k⁻²` satisfies the block hypothesis of `level_sum_blocks` (Epoch's
`block_Ico_padic`). -/
lemma inv_sq_blocks (hp5 : 5 ≤ p) (s : ℕ) (hs : 1 ≤ s) (n : ℕ) :
    (p : ℤ_[p]) ^ s ∣ ∑ k ∈ (Ico (n * p ^ s) ((n + 1) * p ^ s)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2 := by
  rw [← Epoch361883.toZModPow_eq_zero_iff_dvd, show (n + 1) * p ^ s = n * p ^ s + p ^ s by ring]
  exact Epoch361883.block_Ico_padic p s (n * p ^ s) hp5 hs

end general

end OSS
