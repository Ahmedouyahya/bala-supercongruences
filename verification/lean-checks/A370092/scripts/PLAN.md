# A370092 — Lean route (2026-10-16): fully elementary, no Amice theorem

Target `FormalConjectures/OEIS/Auto/370092_862cfcda.lean`: `a : ℕ → ℚ` by the recurrence
a(0) = 1, a(n) = (−1)^n + ½ Σ_{j=1}^{n} (1 − (−1)^j − (−2)^j) C(n,j) a(n−j); `a_mod_k k n := Int.cast (a n).num : ZMod k`;
`oeis_370092_conjecture_0 (k) (hk : 2 < k) : ∃ P, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P`.
Plan: P := φ(k) itself; show k ∣ A(n+φ(k)) − A(n) for n ≥ k, where A : ℕ → ℤ with a n = A n.

## Notation
D(c,k,n) := Σ_{j≤k} (−1)^{k−j} C(k,j) (j+c)^n ∈ ℤ (c ∈ ℤ).   (D(0,k,n) = k!·S(n,k).)
g : ℕ → ℚ, g0 = g1 = g2 = 1, 2 g_k = 2 g_{k−2} + g_{k−3} (k ≥ 3)  [G(u) = (1+u)/(1 − u² − u³/2) = Σ g_k u^k].
h_k := 2^{⌊k/3⌋} g_k ∈ ℤ (induction: h_k = 2^{⌊k/3⌋−⌊(k−2)/3⌋} h_{k−2} + h_{k−3}, exponent ∈ {0,1}).

## Part 1: formula and integrality
1. D(c,k,0) = [k = 0];  D(c,k,n+1) = c·D(c,k,n) + k·D(c+1,k−1,n)  (from (j+c)^{n+1} = (j+c)(j+c)^n and j·C(k,j) = k·C(k−1,j−1)).
   Hence by induction on n (for all c, k): D(c,k,n) = 0 for k > n, and k! ∣ D(c,k,n).
2. Pascal: D(c+1,k,n) = D(c,k,n) + D(c,k+1,n).
3. A(n) := Σ_{k≤n} g_k D(0,k,n) ∈ ℚ. Binomial convolution: for c ∈ ℤ, Σ_{j≤n} C(n,j) c^j A(n−j) = Σ_{k≤n} g_k D(c,k,n)
   (expand (l + c)^n binomially; use item 1 to extend all k-sums to a common bound).
4. With 2 and the recurrence of g:  Σ_k g_k [D(0,k,n) − D(1,k,n) + D(−1,k,n) + D(−2,k,n)] = Σ_k g_k [2E_k − 2E_{k+2} − E_{k+3}],
   E_s := D(−2,s,n), = 2E_0 + 2E_1 = 2(−1)^n. So A satisfies Σ_{j≤n} C(n,j) A(n−j)·[δ_{j0} − 1 + (−1)^j + (−2)^j]/2 = (−1)^n,
   which is the target recurrence (its j = 0 term is −a(n)); strong induction gives a(n) = A(n).
5. Integrality: 2^{⌊k/3⌋} ∣ k! (v_2(k!) ≥ ⌊k/2⌋ ≥ ⌊k/3⌋) ∣ D(0,k,n), so A(n) = Σ_k h_k · D(0,k,n)/2^{⌊k/3⌋} ∈ ℤ; then (a n).num = A n.
   Checked: `numerics/scripts/a370092_powers_of_two.py` (identity (1) of proofs/A370092.md).

## Part 2: odd prime powers (q = p^α, p odd, P = φ(q), n ≥ α)
b_k(n,P) := D(0,k,n+P) − D(0,k,n) = Σ_j (−1)^{k−j} C(k,j) j^n (j^P − 1); each term ≡ 0 mod q (p | j: j^n ≡ 0 as n ≥ α; p ∤ j: Euler).
2^{⌊k/3⌋} ∣ b_k and gcd(q, 2) = 1 ⇒ q ∣ b_k / 2^{⌊k/3⌋}. Sum over k ≤ n+P.

## Part 3: powers of two (q = 2^α, α ≥ 2, m := α − 1 ≥ 1, P = 2^m, n ≥ m+2)  — replaces Amice's theorem
Need Lemma B: v_2(b_k) ≥ m + 1 + ⌊k/3⌋ (then 2^α ∣ b_k/2^{⌊k/3⌋}). For α = 1: from α = 2 (period 2, modulus 4 ⇒ 2).
Let f(x) = x^n (x^{2^m} − 1), k = 2a + e (e ∈ {0,1}), Δ^b[φ](0) := Σ_{t≤b} (−1)^{b−t} C(b,t) φ(t).
(i) Operator identity, from (y−1)^k = (y−1)^e ((y²−1) − 2(y−1))^a and the linear map y^s ↦ f(s) (any f : ℕ → ℤ):
    Σ_{j≤k} (−1)^{k−j} C(k,j) f(j) = Σ_{i≤a} C(a,i) (−2)^i Σ_{l≤i+e} (−1)^{i+e−l} C(i+e,l) Δ^{a−i}[t ↦ f(l+2t)](0).
    (Lean: Polynomial ℤ, Φ_f(p) := p.sum (fun s c ↦ c * f s), (X−1)^k = Σ_i C(a,i)(−2)^i (X−1)^{i+e}(X²−1)^{a−i}.)
(ii) Polynomial lemma: for Q ∈ ℤ[X], b! ∣ Δ^b[Q.eval](0)  (monomials: item 1 with c = 0). With content: Q ∈ 2^s ℤ[X] ⇒ 2^s b! ∣ Δ^b[Q](0).
(iii) Key polynomial fact: for m ≥ 1, ∃ R ∈ ℤ[X], (1+2X)^{2^m} = 1 + 2^{m+1} X(X+1) + 2^{m+2} R
    (m = 1: R = 0; step: square, the cross terms have 2^{2m+2} ⊆ 2^{m+3}).
(iv) Classes: Q_l(t) := f(l + 2t). l even: Q_l = 2^n (l/2 + t)^n (…) ∈ 2^n ℤ[t] ⊆ 2^{m+2} ℤ[t] (n ≥ m+2).
    l odd, l = 2l'+1: by (iii) with X = t + l', Q_l ∈ 2^{m+1} ℤ[t]; and Q_1(t) = 2^{m+1} t(t+1) + 2^{m+2} Q*(t), Q* ∈ ℤ[t]
    (use (1+2t)^n = 1 + 2t·W(t)).
(v) Bound (2): term i of (i) has v_2 ≥ m+1 + i + v_2(C(a,i)) + v_2((a−i)!) = m+1 + v_2(a!) + (i − v_2(i!)), and i − v_2(i!) ≥ 1 for i ≥ 1,
    ≥ 0 always. So v_2(b_k) ≥ m+1+v_2(a!).
(vi) Refinement (2') for a ≠ 2: terms i ≥ 1 have v_2 ≥ m+2+v_2(a!). Term i = 0: e = 0 → only l = 0 (even class, 2^{m+2} a!).
    e = 1 → −Δ^a[Q_0](0) + Δ^a[Q_1](0); Δ^a[Q_1](0) = 2^{m+1} Δ^a[t(t+1)](0) + 2^{m+2}·(a!·ℤ), and Δ^a[t(t+1)](0) = 0 (a = 0),
    2 (a = 1), 2 (a = 2), 0 (a ≥ 3); so for a ≠ 2 it lies in 2^{m+2} a! ℤ. Hence v_2(b_k) ≥ m+2+v_2(a!) for a ≠ 2.
(vii) Lemma B: a = 2 (k ∈ {4,5}): (2) gives m+2 = m+1+⌊k/3⌋. a ≠ 2: (2') and v_2(⌊k/2⌋!) ≥ ⌊k/3⌋ − 1
    (Legendre: v_2(a!) ≥ ⌊a/2⌋ + ⌊a/4⌋ ≥ ⌊k/3⌋ − 1 for a ≥ 7; a ≤ 6 by `decide`).
Numerical check of (2), (2'), Lemma B (m = 1..7, n ≤ m+29, k ≤ 55; ~11,000 cases each, 0 failures, min slack 0) and of
v_2(⌊k/2⌋!) ≥ ⌊k/3⌋ − 1 (k ≤ 2000): `elementary_lemmaB_test.py`.

## Part 4: assembly
For each prime power q = p^α ∥ k: φ(q) ∣ φ(k) (multiplicativity, Mathlib `Nat.totient_mul`, coprime parts), and for p = 2, α = 1:
k > 2 ⇒ odd part ≥ 3 ⇒ 2 ∣ φ(k). Iterating a(n + P_q) ≡ a(n) mod q gives a(n + φ(k)) ≡ a(n) mod q for n ≥ (start).
All prime-power congruences ⇒ k ∣ A(n+φ(k)) − A(n) (Mathlib: `Nat.factorization_prod_pow_eq_self`, coprime product divisibility,
or `Int.dvd_of_forall_prime_pow_dvd`-type lemma). Start N := k (≥ α + 2 for every α ≤ log₂ k... use N := k + 2 to be safe).
Then (a n).num = A n and ZMod.intCast equality ⇔ divisibility.
