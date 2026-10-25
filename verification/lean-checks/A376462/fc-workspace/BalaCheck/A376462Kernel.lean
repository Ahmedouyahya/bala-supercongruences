import BalaCheck.OSSLib

/-!
# A376462, part 2: the self-similar kernels (`proofs/A376462-first-congruence.md`, §2–§3)

Kernels (level `L`, argument `n`):
* `Ψ_1(L,n) = Σ_{i ≤ L} C(L-1,n)² C(L+n,n) C(L,i)² C(2L-n-1-i, L)` (`Psi1`, summand `H1`),
* `Ψ_2(L,n) = Σ_{k ≤ L} C(L-1,n)² C(L,k)² C(L+k,k) C(2L-n-1-k, L)` (`Psi2`, summand `H2`).

* `Psi1_level`, `Psi2_level` (Lemma 7): `p^t ∣ Ψ_j(m p^t, n) - Ψ_j(m p^(t-1), ⌊n/p⌋)`.
* `redK`, `redI`: the level-`N` summands of classes (K), (I) (after removing `N² k⁻²`)
  reduce mod `p^r` to the level-`M` kernel summands.
* `SK_dvd`, `SI_dvd`: `p^r ∣ S_K`, `p^r ∣ S_I` (via `OSS.level_sum_blocks`, `OSS.inv_sq_blocks`).
-/

open Nat Finset

namespace A376462Proof

/-- Summand of `Ψ_1`: `C(L-1,n)² C(L+n,n) C(L,i)² C(2L-n-1-i, L)`. -/
def H1 (L n i : ℕ) : ℕ :=
  (L - 1).choose n ^ 2 * (L + n).choose n * L.choose i ^ 2 * (2 * L - n - 1 - i).choose L

/-- The kernel `Ψ_1(L, n)`. -/
def Psi1 (L n : ℕ) : ℕ := ∑ i ∈ range (L + 1), H1 L n i

/-- Summand of `Ψ_2`: `C(L-1,n)² C(L,k)² C(L+k,k) C(2L-n-1-k, L)`. -/
def H2 (L n k : ℕ) : ℕ :=
  (L - 1).choose n ^ 2 * L.choose k ^ 2 * (L + k).choose k * (2 * L - n - 1 - k).choose L

/-- The kernel `Ψ_2(L, n)`. -/
def Psi2 (L n : ℕ) : ℕ := ∑ k ∈ range (L + 1), H2 L n k

/-- Class (K) summand at level `N` with `N² k⁻²` removed:
`C(N-1,k-1)² C(N+k,k) C(N,pI)² C(2N-k-pI, N)`. -/
def GK (p N k I : ℕ) : ℕ :=
  (N - 1).choose (k - 1) ^ 2 * (N + k).choose k * N.choose (p * I) ^ 2
    * (2 * N - k - p * I).choose N

/-- Class (I) summand at level `N` with `N² i⁻²` removed:
`C(N-1,i-1)² C(N,pK)² C(N+pK,pK) C(2N-pK-i, N)`. -/
def GI (p N i K : ℕ) : ℕ :=
  (N - 1).choose (i - 1) ^ 2 * N.choose (p * K) ^ 2 * (N + p * K).choose (p * K)
    * (2 * N - p * K - i).choose N

/-- Product of four congruences. -/
lemma prod4_dvd {R : Type*} [CommRing R] (d a1 a2 a3 a4 b1 b2 b3 b4 : R)
    (h1 : d ∣ a1 - b1) (h2 : d ∣ a2 - b2) (h3 : d ∣ a3 - b3) (h4 : d ∣ a4 - b4) :
    d ∣ a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4 := by
  have e : a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4
      = (a1 - b1) * a2 * a3 * a4 + b1 * (a2 - b2) * a3 * a4 + b1 * b2 * (a3 - b3) * a4
        + b1 * b2 * b3 * (a4 - b4) := by ring
  rw [e]
  exact dvd_add (dvd_add (dvd_add (((h1.mul_right _).mul_right _).mul_right _)
    (((h2.mul_left _).mul_right _).mul_right _)) ((h3.mul_left _).mul_right _)) (h4.mul_left _)

lemma sq_sub_dvd {R : Type*} [CommRing R] (d x y : R) (h : d ∣ x - y) : d ∣ x ^ 2 - y ^ 2 := by
  have e : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [e]
  exact h.mul_right _

/-- `C(N,k) k = N C(N-1,k-1)`. -/
lemma choose_mul_self (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    N.choose k * k = N * (N - 1).choose (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact (Nat.add_one_mul_choose_eq n j).symm

section padic

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
lemma lev (m t : ℕ) (ht : 1 ≤ t) : m * p ^ t = p * (m * p ^ (t - 1)) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

omit [Fact p.Prime] in
/-- `⌊(2pL - n - 1 - pi)/p⌋ = 2L - ⌊n/p⌋ - 1 - i` (truncated subtraction, all `n`, `i`). -/
lemma div_lemma (hp : 0 < p) (L n i : ℕ) :
    (2 * (p * L) - n - 1 - p * i) / p = 2 * L - n / p - 1 - i := by
  have hn := Nat.div_add_mod n p
  have hρ := Nat.mod_lt n hp
  generalize n / p = q at hn ⊢
  generalize n % p = ρ at hn hρ
  subst hn
  rcases le_or_gt (q + 1 + i) (2 * L) with h | h
  · obtain ⟨d, hd⟩ : ∃ d, 2 * L = q + 1 + i + d := ⟨2 * L - (q + 1 + i), by omega⟩
    have e1 : 2 * (p * L) = p * q + p + p * i + p * d := by
      have : 2 * (p * L) = p * (2 * L) := by ring
      rw [this, hd]
      ring
    have e2 : 2 * (p * L) - (p * q + ρ) - 1 - p * i = (p - 1 - ρ) + p * d := by
      rw [e1]
      omega
    rw [e2, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]
    omega
  · have e1 : p * (2 * L) ≤ p * (q + i) := Nat.mul_le_mul_left p (by omega)
    have e3 : p * (q + i) = p * q + p * i := by ring
    have e4 : 2 * (p * L) = p * (2 * L) := by ring
    have e2 : 2 * (p * L) - (p * q + ρ) - 1 - p * i = 0 := by omega
    rw [e2, Nat.zero_div]
    omega

/-- Splitting a sum over `range (m p^t + 1)` by divisibility by `p`. -/
lemma split_lev (m t : ℕ) (ht : 1 ≤ t) (f : ℕ → ℤ) :
    ∑ i ∈ range (m * p ^ t + 1), f i = ∑ j ∈ range (m * p ^ (t - 1) + 1), f (p * j)
      + ∑ i ∈ (range (m * p ^ t + 1)).filter (fun i => ¬ p ∣ i), f i := by
  rw [lev p m t ht]
  exact OSS.sum_split_dvd p _ f

/-- `p^r ∣ C(N,k)` when `p^r ∣ N` and `p ∤ k`. -/
lemma choose_dvd_of_not_dvd (N r k : ℕ) (hN : p ^ r ∣ N) (hk : ¬ p ∣ k) : p ^ r ∣ N.choose k := by
  have hp : p.Prime := Fact.out
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (dvd_zero p) hk
    · exact h
  rcases Nat.eq_zero_or_pos N with h0 | hN1
  · subst h0
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact dvd_zero _
  have h1 := choose_mul_self N k hN1 hk1
  have h2 : p ^ r ∣ N.choose k * k := by
    rw [h1]
    exact hN.mul_right _
  exact (Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)).dvd_of_dvd_mul_right h2

/-- Lemma 3, squared (the sign disappears). -/
lemma cA (m t n : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (((m * p ^ t - 1).choose n : ℕ) : ℤ) ^ 2
      - (((m * p ^ (t - 1) - 1).choose (n / p) : ℕ) : ℤ) ^ 2 := by
  have h := sq_sub_dvd _ _ _ (OSS.lemma3_int p m t n hm ht)
  have hs : ∀ j : ℕ, ((-1 : ℤ) ^ j) ^ 2 = 1 := fun j => by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  rwa [mul_pow, mul_pow, hs, hs, one_mul, one_mul] at h

lemma cA_pred (m t k : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) (hk : ¬ p ∣ k) :
    (p : ℤ) ^ t ∣ (((m * p ^ t - 1).choose (k - 1) : ℕ) : ℤ) ^ 2
      - (((m * p ^ (t - 1) - 1).choose (k / p) : ℕ) : ℤ) ^ 2 := by
  have h := cA p m t (k - 1) hm ht
  rwa [OSS.pred_div_eq p k hk] at h

/-- Lemma 4(i) at a multiple of `p`. -/
lemma cB' (m t j : ℕ) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (((m * p ^ t + p * j).choose (p * j) : ℕ) : ℤ)
      - (((m * p ^ (t - 1) + j).choose j : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  have h := OSS.lemma4i_int p m t (p * j) ht
  rwa [Nat.mul_div_cancel_left j hp.pos] at h

/-- Lemma 1 (Kazandzidis) mod `p^t`: `C(m p^t, p i) ≡ C(m p^(t-1), i)`. -/
lemma cC (hp5 : 5 ≤ p) (m t i : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (((m * p ^ t).choose (p * i) : ℕ) : ℤ) - (((m * p ^ (t - 1)).choose i : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  have h := OSS.kaz_int p hp5 (m * p ^ (t - 1)) i
  rw [← lev p m t ht] at h
  have hv : t - 1 ≤ (m * p ^ (t - 1)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))).mp
      (dvd_mul_left _ _)
  exact (pow_dvd_pow _ (by omega)).trans h

/-- Lemma 4(ii) with the floor computed. -/
lemma cD (m t n i : ℕ) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (((2 * (m * p ^ t) - n - 1 - p * i).choose (m * p ^ t) : ℕ) : ℤ)
      - (((2 * (m * p ^ (t - 1)) - n / p - 1 - i).choose (m * p ^ (t - 1)) : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  have h := OSS.lemma4ii_int p m t (2 * (m * p ^ t) - n - 1 - p * i) ht
  rw [lev p m t ht, div_lemma p hp.pos] at h
  rw [lev p m t ht]
  exact h

/-- `p^t ∣ C(m p^t, i)` for `p ∤ i`. -/
lemma cZ (m t i : ℕ) (hi : ¬ p ∣ i) : (p : ℤ) ^ t ∣ (((m * p ^ t).choose i : ℕ) : ℤ) := by
  have h := choose_dvd_of_not_dvd p (m * p ^ t) t i (dvd_mul_left _ _) hi
  exact_mod_cast Int.natCast_dvd_natCast.mpr h

lemma H1_level (hp5 : 5 ≤ p) (m t n j : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (H1 (m * p ^ t) n (p * j) : ℤ) - (H1 (m * p ^ (t - 1)) (n / p) j : ℤ) := by
  unfold H1
  push_cast
  exact prod4_dvd _ _ _ _ _ _ _ _ _ (cA p m t n hm ht) (OSS.lemma4i_int p m t n ht)
    (sq_sub_dvd _ _ _ (cC p hp5 m t j hm ht)) (cD p m t n j ht)

lemma H2_level (hp5 : 5 ≤ p) (m t n j : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (H2 (m * p ^ t) n (p * j) : ℤ) - (H2 (m * p ^ (t - 1)) (n / p) j : ℤ) := by
  unfold H2
  push_cast
  exact prod4_dvd _ _ _ _ _ _ _ _ _ (cA p m t n hm ht) (sq_sub_dvd _ _ _ (cC p hp5 m t j hm ht))
    (cB' p m t j ht) (cD p m t n j ht)

/-- **Lemma 7** for `Ψ_1`. -/
lemma Psi1_level (hp5 : 5 ≤ p) (m t n : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (Psi1 (m * p ^ t) n : ℤ) - (Psi1 (m * p ^ (t - 1)) (n / p) : ℤ) := by
  unfold Psi1
  push_cast
  rw [split_lev p m t ht, add_sub_right_comm, ← Finset.sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j _
    exact H1_level p hp5 m t n j hm ht
  · apply Finset.dvd_sum
    intro i hi
    have hz := cZ p m t i (mem_filter.mp hi).2
    unfold H1
    push_cast
    exact ((dvd_pow hz two_ne_zero).mul_left _).mul_right _

/-- **Lemma 7** for `Ψ_2`. -/
lemma Psi2_level (hp5 : 5 ≤ p) (m t n : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (p : ℤ) ^ t ∣ (Psi2 (m * p ^ t) n : ℤ) - (Psi2 (m * p ^ (t - 1)) (n / p) : ℤ) := by
  unfold Psi2
  push_cast
  rw [split_lev p m t ht, add_sub_right_comm, ← Finset.sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j _
    exact H2_level p hp5 m t n j hm ht
  · apply Finset.dvd_sum
    intro i hi
    have hz := cZ p m t i (mem_filter.mp hi).2
    unfold H2
    push_cast
    exact (((dvd_pow hz two_ne_zero).mul_left _).mul_right _).mul_right _

/-- Class (K) summand reduces to the `Ψ_1` summand mod `p^r`. -/
lemma redK (hp5 : 5 ≤ p) (m r k I : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) (hk : ¬ p ∣ k) :
    (p : ℤ) ^ r ∣ (GK p (m * p ^ r) k I : ℤ) - (H1 (m * p ^ (r - 1)) (k / p) I : ℤ) := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (dvd_zero p) hk
    · exact h
  have h4 := cD p m r (k - 1) I hr
  rw [OSS.pred_div_eq p k hk,
    show 2 * (m * p ^ r) - (k - 1) - 1 - p * I = 2 * (m * p ^ r) - k - p * I by omega] at h4
  unfold GK H1
  push_cast
  exact prod4_dvd _ _ _ _ _ _ _ _ _ (cA_pred p m r k hm hr hk) (OSS.lemma4i_int p m r k hr)
    (sq_sub_dvd _ _ _ (cC p hp5 m r I hm hr)) h4

/-- Class (I) summand reduces to the `Ψ_2` summand mod `p^r`. -/
lemma redI (hp5 : 5 ≤ p) (m r i K : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) (hi : ¬ p ∣ i) :
    (p : ℤ) ^ r ∣ (GI p (m * p ^ r) i K : ℤ) - (H2 (m * p ^ (r - 1)) (i / p) K : ℤ) := by
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact absurd (dvd_zero p) hi
    · exact h
  have h4 := cD p m r (i - 1) K hr
  rw [OSS.pred_div_eq p i hi,
    show 2 * (m * p ^ r) - (i - 1) - 1 - p * K = 2 * (m * p ^ r) - p * K - i by omega] at h4
  unfold GI H2
  push_cast
  exact prod4_dvd _ _ _ _ _ _ _ _ _ (cA_pred p m r i hm hr hi)
    (sq_sub_dvd _ _ _ (cC p hp5 m r K hm hr)) (cB' p m r K hr) h4

/-- `p^r ∣ S_K` (§2). -/
lemma SK_dvd (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2
        * ∑ I ∈ range (m * p ^ (r - 1) + 1), ((GK p (m * p ^ r) k I : ℕ) : ℤ_[p]) := by
  have hlev := OSS.level_sum_blocks p r m hr (fun k => Ring.inverse (k : ℤ_[p]) ^ 2)
    (fun s hs1 _ n => OSS.inv_sq_blocks p hp5 s hs1 n)
    (fun t n => (Psi1 (m * p ^ t) n : ℤ))
    (fun t ht1 _ n => Psi1_level p hp5 m t n hm ht1)
  have hdiff : (p : ℤ_[p]) ^ r ∣ ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2
        * (((∑ I ∈ range (m * p ^ (r - 1) + 1), (GK p (m * p ^ r) k I : ℤ))
          - (Psi1 (m * p ^ (r - 1)) (k / p) : ℤ) : ℤ) : ℤ_[p]) := by
    apply Finset.dvd_sum
    intro k hk
    apply Dvd.dvd.mul_left
    rw [← A386548.int_dvd_iff_padic_dvd]
    unfold Psi1
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro I _
    exact redK p hp5 m r k I hm hr (mem_filter.mp hk).2
  have e : ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
      Ring.inverse (k : ℤ_[p]) ^ 2
        * ∑ I ∈ range (m * p ^ (r - 1) + 1), ((GK p (m * p ^ r) k I : ℕ) : ℤ_[p])
      = ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2 * (((Psi1 (m * p ^ (r - 1)) (k / p) : ℤ) : ℤ_[p]))
        + ∑ k ∈ (range (m * p ^ r)).filter (fun k => ¬ p ∣ k),
          Ring.inverse (k : ℤ_[p]) ^ 2
            * (((∑ I ∈ range (m * p ^ (r - 1) + 1), (GK p (m * p ^ r) k I : ℤ))
              - (Psi1 (m * p ^ (r - 1)) (k / p) : ℤ) : ℤ) : ℤ_[p]) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [e]
  exact dvd_add hlev hdiff

/-- `p^r ∣ S_I` (§3). -/
lemma SI_dvd (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ r ∣ ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
      Ring.inverse (i : ℤ_[p]) ^ 2
        * ∑ K ∈ range (m * p ^ (r - 1) + 1), ((GI p (m * p ^ r) i K : ℕ) : ℤ_[p]) := by
  have hlev := OSS.level_sum_blocks p r m hr (fun k => Ring.inverse (k : ℤ_[p]) ^ 2)
    (fun s hs1 _ n => OSS.inv_sq_blocks p hp5 s hs1 n)
    (fun t n => (Psi2 (m * p ^ t) n : ℤ))
    (fun t ht1 _ n => Psi2_level p hp5 m t n hm ht1)
  have hdiff : (p : ℤ_[p]) ^ r ∣ ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
      Ring.inverse (i : ℤ_[p]) ^ 2
        * (((∑ K ∈ range (m * p ^ (r - 1) + 1), (GI p (m * p ^ r) i K : ℤ))
          - (Psi2 (m * p ^ (r - 1)) (i / p) : ℤ) : ℤ) : ℤ_[p]) := by
    apply Finset.dvd_sum
    intro i hi
    apply Dvd.dvd.mul_left
    rw [← A386548.int_dvd_iff_padic_dvd]
    unfold Psi2
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro K _
    exact redI p hp5 m r i K hm hr (mem_filter.mp hi).2
  have e : ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
      Ring.inverse (i : ℤ_[p]) ^ 2
        * ∑ K ∈ range (m * p ^ (r - 1) + 1), ((GI p (m * p ^ r) i K : ℕ) : ℤ_[p])
      = ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
          Ring.inverse (i : ℤ_[p]) ^ 2 * (((Psi2 (m * p ^ (r - 1)) (i / p) : ℤ) : ℤ_[p]))
        + ∑ i ∈ (range (m * p ^ r)).filter (fun i => ¬ p ∣ i),
          Ring.inverse (i : ℤ_[p]) ^ 2
            * (((∑ K ∈ range (m * p ^ (r - 1) + 1), (GI p (m * p ^ r) i K : ℤ))
              - (Psi2 (m * p ^ (r - 1)) (i / p) : ℤ) : ℤ) : ℤ_[p]) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [e]
  exact dvd_add hlev hdiff

end padic

end A376462Proof
