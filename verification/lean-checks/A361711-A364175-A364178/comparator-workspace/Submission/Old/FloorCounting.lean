import Mathlib

/-!
# Counting and floor lemmas for the integrality proofs of §1 of
`notes/A364175-A364178-factorial-ratio-towers.md`

* `mul_div_decompose`: `a n / Q = a (n / Q) + a (n % Q) / Q`;
* `card_filter_le_div_add`: for `gcd(Q, d) = 1`, `#{1 ≤ j ≤ n : Q ∣ u n + d j} ≤ n / Q + [Q ≤ (u+d)(n % Q)]`
  (at most one solution per block of `Q` consecutive integers; none in the last partial block
  unless `(u+d)(n % Q) ≥ Q`);
* the finite floor checks (`floor_ineq_b`, `floor_ineq_vas`, …), reduced to a `decide` over
  `k = L ρ / Q < L`;
* Legendre bookkeeping: `padicValNat_factorial_of_lt`, `padicValNat_finset_prod`,
  `padicValNat_prod_linear`.
-/

open Finset

namespace Bala

theorem mul_div_decompose (a m Q : ℕ) (hQ : 0 < Q) :
    a * m / Q = a * (m / Q) + a * (m % Q) / Q := by
  have h : a * m = a * (m % Q) + Q * (a * (m / Q)) := by
    have := Nat.div_add_mod m Q
    calc a * m = a * (Q * (m / Q) + m % Q) := by rw [this]
      _ = a * (m % Q) + Q * (a * (m / Q)) := by ring
  rw [h, Nat.add_mul_div_left _ _ hQ, add_comm]

/-- `c ρ / Q = (c k ρ / Q) / k` -/
theorem div_scale (c k ρ Q : ℕ) (hk : 0 < k) : c * ρ / Q = c * k * ρ / Q / k := by
  rw [Nat.div_div_eq_div_mul, show c * k * ρ = k * (c * ρ) by ring, show Q * k = k * Q by ring,
    Nat.mul_div_mul_left _ _ hk]

theorem div_lt_of_lt (L ρ Q : ℕ) (hL : 0 < L) (hQ : 0 < Q) (hρ : ρ < Q) : L * ρ / Q < L := by
  rw [Nat.div_lt_iff_lt_mul hQ]
  exact Nat.mul_lt_mul_of_pos_left hρ hL

/-! ### Finite floor checks -/

theorem check_b : ∀ k, k < 30 → k / 5 + k / 6 + (if 10 ≤ k then 1 else 0) ≤ k / 3 + k / 10 := by
  decide

theorem check_vas : ∀ k, k < 60 → k / 5 + k / 6 + k / 30 + k / 20 ≤ k / 3 + k / 10 + k / 60 := by
  decide

theorem check_a : ∀ k, k < 30 → k / 10 + k / 15 + (if 6 ≤ k then 1 else 0) ≤ k / 5 := by
  decide

theorem check_vas_a : ∀ k, k < 90 → k / 10 + k / 15 + k / 18 ≤ k / 5 + k / 45 := by
  decide

/-- the floor inequality for A364178: `⌊6x⌋ + ⌊5x⌋ + [x ≥ 1/3] ≤ ⌊10x⌋ + ⌊3x⌋` on `[0,1)` -/
theorem floor_ineq_b (Q ρ : ℕ) (hQ : 0 < Q) (hρ : ρ < Q) :
    6 * ρ / Q + 5 * ρ / Q + (if Q ≤ 3 * ρ then 1 else 0) ≤ 10 * ρ / Q + 3 * ρ / Q := by
  have h10 : 10 * ρ / Q = 30 * ρ / Q / 3 := by
    have := div_scale 10 3 ρ Q (by norm_num)
    rwa [show 10 * 3 = 30 by norm_num] at this
  have h3 : 3 * ρ / Q = 30 * ρ / Q / 10 := by
    have := div_scale 3 10 ρ Q (by norm_num)
    rwa [show 3 * 10 = 30 by norm_num] at this
  have h6 : 6 * ρ / Q = 30 * ρ / Q / 5 := by
    have := div_scale 6 5 ρ Q (by norm_num)
    rwa [show 6 * 5 = 30 by norm_num] at this
  have h5 : 5 * ρ / Q = 30 * ρ / Q / 6 := by
    have := div_scale 5 6 ρ Q (by norm_num)
    rwa [show 5 * 6 = 30 by norm_num] at this
  have hind : (Q ≤ 3 * ρ) ↔ 10 ≤ 30 * ρ / Q := by
    rw [Nat.le_div_iff_mul_le hQ]
    constructor <;> intro h <;> omega
  have hlt : 30 * ρ / Q < 30 := div_lt_of_lt 30 ρ Q (by norm_num) hQ hρ
  have hite : (if Q ≤ 3 * ρ then 1 else 0) = (if 10 ≤ 30 * ρ / Q then 1 else 0) := by
    simp only [hind]
  rw [h10, h3, h6, h5, hite]
  exact check_b _ hlt

/-- the Landau inequality of the Vasyunin ratio `(20m)!(6m)!m!/((12m)!(10m)!(3m)!(2m)!)` -/
theorem floor_ineq_vas (Q ρ : ℕ) (hQ : 0 < Q) (hρ : ρ < Q) :
    12 * ρ / Q + 10 * ρ / Q + 2 * ρ / Q + 3 * ρ / Q ≤ 20 * ρ / Q + 6 * ρ / Q + ρ / Q := by
  have h12 : 12 * ρ / Q = 60 * ρ / Q / 5 := by
    have := div_scale 12 5 ρ Q (by norm_num)
    rwa [show 12 * 5 = 60 by norm_num] at this
  have h10 : 10 * ρ / Q = 60 * ρ / Q / 6 := by
    have := div_scale 10 6 ρ Q (by norm_num)
    rwa [show 10 * 6 = 60 by norm_num] at this
  have h2 : 2 * ρ / Q = 60 * ρ / Q / 30 := by
    have := div_scale 2 30 ρ Q (by norm_num)
    rwa [show 2 * 30 = 60 by norm_num] at this
  have h3 : 3 * ρ / Q = 60 * ρ / Q / 20 := by
    have := div_scale 3 20 ρ Q (by norm_num)
    rwa [show 3 * 20 = 60 by norm_num] at this
  have h20 : 20 * ρ / Q = 60 * ρ / Q / 3 := by
    have := div_scale 20 3 ρ Q (by norm_num)
    rwa [show 20 * 3 = 60 by norm_num] at this
  have h6 : 6 * ρ / Q = 60 * ρ / Q / 10 := by
    have := div_scale 6 10 ρ Q (by norm_num)
    rwa [show 6 * 10 = 60 by norm_num] at this
  have h1 : ρ / Q = 60 * ρ / Q / 60 := by
    have := div_scale 1 60 ρ Q (by norm_num)
    rwa [show 1 * 60 = 60 by norm_num, one_mul] at this
  have hlt : 60 * ρ / Q < 60 := div_lt_of_lt 60 ρ Q (by norm_num) hQ hρ
  rw [h12, h10, h2, h3, h20, h6, h1]
  exact check_vas _ hlt

/-- the floor inequality for A364175: `⌊3x⌋ + ⌊2x⌋ + [x ≥ 1/5] ≤ ⌊6x⌋` on `[0,1)` -/
theorem floor_ineq_a (Q ρ : ℕ) (hQ : 0 < Q) (hρ : ρ < Q) :
    3 * ρ / Q + 2 * ρ / Q + (if Q ≤ 5 * ρ then 1 else 0) ≤ 6 * ρ / Q := by
  have h3 : 3 * ρ / Q = 30 * ρ / Q / 10 := by
    have := div_scale 3 10 ρ Q (by norm_num)
    rwa [show 3 * 10 = 30 by norm_num] at this
  have h2 : 2 * ρ / Q = 30 * ρ / Q / 15 := by
    have := div_scale 2 15 ρ Q (by norm_num)
    rwa [show 2 * 15 = 30 by norm_num] at this
  have h6 : 6 * ρ / Q = 30 * ρ / Q / 5 := by
    have := div_scale 6 5 ρ Q (by norm_num)
    rwa [show 6 * 5 = 30 by norm_num] at this
  have hind : (Q ≤ 5 * ρ) ↔ 6 ≤ 30 * ρ / Q := by
    rw [Nat.le_div_iff_mul_le hQ]
    constructor <;> intro h <;> omega
  have hlt : 30 * ρ / Q < 30 := div_lt_of_lt 30 ρ Q (by norm_num) hQ hρ
  have hite : (if Q ≤ 5 * ρ then 1 else 0) = (if 6 ≤ 30 * ρ / Q then 1 else 0) := by
    simp only [hind]
  rw [h3, h2, h6, hite]
  exact check_a _ hlt

/-- the Landau inequality of the Vasyunin ratio `(18m)!(2m)!/((9m)!(6m)!(5m)!)` -/
theorem floor_ineq_vas_a (Q ρ : ℕ) (hQ : 0 < Q) (hρ : ρ < Q) :
    9 * ρ / Q + 6 * ρ / Q + 5 * ρ / Q ≤ 18 * ρ / Q + 2 * ρ / Q := by
  have h9 : 9 * ρ / Q = 90 * ρ / Q / 10 := by
    have := div_scale 9 10 ρ Q (by norm_num)
    rwa [show 9 * 10 = 90 by norm_num] at this
  have h6 : 6 * ρ / Q = 90 * ρ / Q / 15 := by
    have := div_scale 6 15 ρ Q (by norm_num)
    rwa [show 6 * 15 = 90 by norm_num] at this
  have h5 : 5 * ρ / Q = 90 * ρ / Q / 18 := by
    have := div_scale 5 18 ρ Q (by norm_num)
    rwa [show 5 * 18 = 90 by norm_num] at this
  have h18 : 18 * ρ / Q = 90 * ρ / Q / 5 := by
    have := div_scale 18 5 ρ Q (by norm_num)
    rwa [show 18 * 5 = 90 by norm_num] at this
  have h2 : 2 * ρ / Q = 90 * ρ / Q / 45 := by
    have := div_scale 2 45 ρ Q (by norm_num)
    rwa [show 2 * 45 = 90 by norm_num] at this
  have hlt : 90 * ρ / Q < 90 := div_lt_of_lt 90 ρ Q (by norm_num) hQ hρ
  rw [h9, h6, h5, h18, h2]
  exact check_vas_a _ hlt

/-! ### Counting the solutions of `Q ∣ c + d j` -/

/-- at most one solution in any block of `Q` consecutive integers, when `gcd(Q, d) = 1` -/
theorem card_filter_block_le_one (Q d c a : ℕ) (hcop : Nat.Coprime Q d) :
    ((Icc (a + 1) (a + Q)).filter (fun j => Q ∣ c + d * j)).card ≤ 1 := by
  rw [card_le_one]
  have key : ∀ j j', j ∈ (Icc (a + 1) (a + Q)).filter (fun j => Q ∣ c + d * j) →
      j' ∈ (Icc (a + 1) (a + Q)).filter (fun j => Q ∣ c + d * j) → j ≤ j' → j = j' := by
    intro j j' hj hj' hle
    simp only [mem_filter, mem_Icc] at hj hj'
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
    have h1 : Q ∣ (c + d * (j + e)) - (c + d * j) := Nat.dvd_sub hj'.2 hj.2
    have h2 : (c + d * (j + e)) - (c + d * j) = d * e := by
      rw [mul_add]
      omega
    rw [h2] at h1
    have h3 : Q ∣ e := hcop.dvd_of_dvd_mul_left h1
    have h4 : e < Q := by omega
    have h5 : e = 0 := Nat.eq_zero_of_dvd_of_lt h3 h4
    omega
  intro j hj j' hj'
  rcases le_total j j' with h | h
  · exact key j j' hj hj' h
  · exact (key j' j hj' hj h).symm

theorem card_filter_Icc_le (Q d c ρ : ℕ) (hcop : Nat.Coprime Q d) (t : ℕ) :
    ((Icc 1 (t * Q + ρ)).filter (fun j => Q ∣ c + d * j)).card
      ≤ t + ((Icc 1 ρ).filter (fun j => Q ∣ c + d * j)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hunion : Icc 1 ((t + 1) * Q + ρ)
        = Icc 1 (t * Q + ρ) ∪ Icc (t * Q + ρ + 1) (t * Q + ρ + Q) := by
      rw [add_mul, one_mul]
      ext j
      simp only [mem_Icc, mem_union]
      omega
    have hdisj : Disjoint (Icc 1 (t * Q + ρ)) (Icc (t * Q + ρ + 1) (t * Q + ρ + Q)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [mem_Icc] at hj hj'
      omega
    rw [hunion, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
    have hb := card_filter_block_le_one Q d c (t * Q + ρ) hcop
    omega

theorem card_filter_partial (Q d u n : ℕ) (hQ : 0 < Q) (hd : 0 < d) (hcop : Nat.Coprime Q d) :
    ((Icc 1 (n % Q)).filter (fun j => Q ∣ u * n + d * j)).card
      ≤ if Q ≤ (u + d) * (n % Q) then 1 else 0 := by
  split_ifs with h
  · have hsub : (Icc 1 (n % Q)).filter (fun j => Q ∣ u * n + d * j)
        ⊆ (Icc (0 + 1) (0 + Q)).filter (fun j => Q ∣ u * n + d * j) := by
      apply filter_subset_filter
      intro j hj
      simp only [mem_Icc] at hj ⊢
      have := Nat.mod_lt n hQ
      omega
    exact (card_le_card hsub).trans (card_filter_block_le_one Q d (u * n) 0 hcop)
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro j hj hdvd
    simp only [mem_Icc] at hj
    have h' : (u + d) * (n % Q) < Q := not_le.mp h
    have h1 : u * n + d * j = Q * (u * (n / Q)) + (u * (n % Q) + d * j) := by
      have := Nat.div_add_mod n Q
      calc u * n + d * j = u * (Q * (n / Q) + n % Q) + d * j := by rw [this]
        _ = Q * (u * (n / Q)) + (u * (n % Q) + d * j) := by ring
    rw [h1] at hdvd
    have h2 : Q ∣ u * (n % Q) + d * j := (Nat.dvd_add_right (dvd_mul_right Q _)).mp hdvd
    have h3 : 0 < d * j := Nat.mul_pos hd (by omega)
    have h4 : d * j ≤ d * (n % Q) := Nat.mul_le_mul_left d hj.2
    have h5 : (u + d) * (n % Q) = u * (n % Q) + d * (n % Q) := by ring
    have h6 : u * (n % Q) + d * j < Q := by omega
    exact absurd (Nat.le_of_dvd (by omega) h2) (not_le.mpr h6)

/-- `#{1 ≤ j ≤ n : Q ∣ u n + d j} ≤ n / Q + [Q ≤ (u + d) (n % Q)]` for `gcd(Q, d) = 1`, `d ≥ 1` -/
theorem card_filter_le_div_add (Q d u n : ℕ) (hQ : 0 < Q) (hd : 0 < d) (hcop : Nat.Coprime Q d) :
    ((Icc 1 n).filter (fun j => Q ∣ u * n + d * j)).card
      ≤ n / Q + if Q ≤ (u + d) * (n % Q) then 1 else 0 := by
  have h1 := card_filter_Icc_le Q d (u * n) (n % Q) hcop (n / Q)
  rw [Nat.div_add_mod' n Q] at h1
  have h2 := card_filter_partial Q d u n hQ hd hcop
  split_ifs at h2 ⊢ <;> omega

/-! ### Legendre bookkeeping -/

/-- Legendre's formula with a uniform bound `b > X`. -/
theorem padicValNat_factorial_of_lt (q X b : ℕ) [hq : Fact q.Prime] (hXb : X < b) :
    padicValNat q X.factorial = ∑ i ∈ Ico 1 b, X / q ^ i := by
  apply padicValNat_factorial
  apply Nat.log_lt_of_lt_pow' (by omega)
  calc X < b := hXb
    _ < q ^ b := Nat.lt_pow_self hq.out.one_lt

theorem padicValNat_finset_prod {ι : Type*} (q : ℕ) [hq : Fact q.Prime] (S : Finset ι)
    (g : ι → ℕ) (hg : ∀ x ∈ S, g x ≠ 0) :
    padicValNat q (∏ x ∈ S, g x) = ∑ x ∈ S, padicValNat q (g x) := by
  have h := Nat.factorization_prod hg
  have h2 := congrArg (fun f => f q) h
  simp only [Finsupp.finset_sum_apply, Nat.factorization_def _ hq.out] at h2
  exact h2

/-- the `q`-adic valuation of `∏_{j=1}^{n} (u n + d j)` as a double count -/
theorem padicValNat_prod_linear (q u d n b : ℕ) [hq : Fact q.Prime] (hd : 0 < d)
    (hb : (u + d) * n < b) :
    padicValNat q (∏ j ∈ Icc 1 n, (u * n + d * j))
      = ∑ i ∈ Ico 1 b, ((Icc 1 n).filter (fun j => q ^ i ∣ u * n + d * j)).card := by
  have hne : ∀ j ∈ Icc 1 n, u * n + d * j ≠ 0 := by
    intro j hj
    simp only [mem_Icc] at hj
    have := Nat.mul_pos hd hj.1
    omega
  rw [padicValNat_finset_prod q _ _ hne]
  have hterm : ∀ j ∈ Icc 1 n, padicValNat q (u * n + d * j)
      = ((Ico 1 b).filter (fun i => q ^ i ∣ u * n + d * j)).card := by
    intro j hj
    have hpos : 0 < u * n + d * j := Nat.pos_of_ne_zero (hne j hj)
    have hlog : Nat.log q (u * n + d * j) < b := by
      apply Nat.log_lt_of_lt_pow' (by omega)
      simp only [mem_Icc] at hj
      have hdj : d * j ≤ d * n := Nat.mul_le_mul_left d hj.2
      calc u * n + d * j ≤ (u + d) * n := by rw [add_mul]; omega
        _ < b := hb
        _ < q ^ b := Nat.lt_pow_self hq.out.one_lt
    have := Nat.emultiplicity_eq_card_pow_dvd hq.out.ne_one hpos hlog
    rw [← padicValNat_eq_emultiplicity (hne j hj)] at this
    exact_mod_cast this
  rw [sum_congr rfl hterm]
  simp only [card_filter]
  rw [sum_comm]

end Bala
