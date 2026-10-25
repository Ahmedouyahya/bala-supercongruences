# A333565 in Lean (target `333565_757e3efd.lean`, primes p ≥ 3) — plan of 2026-10-16

## Bridge (elementary; checked in `bridge_test.py`, 0 failures)
b_m = 2^m C(2m,m), d_n = Σ_{k≤n} (−1)^k b_{n−k}, e_n = d_n + 4 [n ≠ 0] d_{n−1} (the target is e_n.toNat).
S(n,K) = Σ_{j≤K} C(n+j−1,j) 2^j;  B(n) = S(n,n) = Σ_k C(2n,n−k) C(n+k−1,k) (A333562Ident `S_eq_R`, m = n−1, K = n).
1. S(n,K) = S(n−1,K) + 2 S(n,K−1) (Pascal on C(n+j−1,j)); with S(n−1,n) = S(n−1,n−1) + 2^n C(2n−2,n) and
   S(n,n−1) = S(n,n) − 2^n C(2n−1,n):  B(n) + B(n−1) = 2^{n+1} C(2n−1,n) − 2^n C(2n−2,n) = 2^n C(2n,n) − 2^n C(2n−2,n−2).
2. d_n + d_{n−1} = b_n, so e_n + e_{n−1} = b_n + 4 b_{n−1} = 2(B(n) + B(n−1)); e_0 = 1 = 2B(0) − 1; induction: e_n = 2B(n) − (−1)^n ≥ 1.
3. For N = pM (p odd): A333565(N) − A333565(M) = 2(B(N) − B(M)); 2 is a unit mod p^(3r).
4. B(n) = coeff n ((1+X)^{2n} (1−X)^{−n}) = A_{(2,−1,1)}(n): p ≥ 5 from Theorem F (`BalaCheck/TF*`).

## p = 3 for (a,b,c) = (2,−1,1) only (Theorem F₃(ii), class a + b ≡ c; `proofs/TheoremF-p-eq-3.md`), on the TF set-up
Notation from TF: Φ M = expS(M F) = φ^M, γ_s = coeff s (Φ M), L = aV − bU (p = 3), λ_M(f) := Σ_{s≤cM} γ_s f_{cM−s}.
5. Expansion (TF step 3 at p = 3): A(3M) − A(M) = Σ_{w<cM} γ_w Σ_{ℓ≥1} (N^ℓ/ℓ!) [x^{3(cM−w)}] L^ℓ, N = 3M, r = 1 + v_3 M.
   ℓ = 1: 0. ℓ ≥ 4: v_3(N^ℓ/ℓ!) ≥ 3r (v_3(ℓ!) ≤ (ℓ−1)/2; ℓ = 4: 4r − 1).
6. Cubic (Lemma D): [x^{3t}]L³ ≡ L_t (mod 3) (Frobenius, Epoch `frob_trunc`), so the ℓ = 3 part ≡ (9M³/2) λ_M(L) mod 3^{3r}.
7. Quadratic: [x^{3t}]L² = t·g_t with g_t ∈ ℤ_(3) (Lemma H(a)); exact-form identity (Lemma A):
   Σ_s γ_s (cM − s) h_{cM−s} = −M λ_M((ψ − c) h), from s γ_s = M Σ_i ψ_i γ_{s−i} (derivative of Φ M = expS(M F):
   `isExpOf_iff_deriv`; ψ := X·F′, ψ_i = ℓ_i = a(−1)^{i+1} − b). So the ℓ = 2 part = −(9M³/2) λ_M((ψ − c) g).
8. Hence A(3M) − A(M) ≡ (9M³/2) λ_M(L − (ψ − c) g) (mod 3^{3r}) and v_3(9M³/2) = 3r − 1: it suffices that
   λ_M(L − (ψ − c) g) ≡ 0 (mod 3), and since γ_s ∈ ℤ, that every coefficient of L − (ψ − c) g is ≡ 0 mod 3.
9. Harmonic sums at p = 3 (Lemmas E, F): S_2 := Σ_{u<3^e, 3∤u} u^{−2} ≡ −3^{e−1} (mod 3^e); 2 S_1 ≡ 3^{2e−1} (mod 3^{2e});
   H_T ≡ −3^{2e−1} (mod 3^{2e}) for T = ℓ 3^e (3 ∤ ℓ); for T even H_T^± = H_T − H_{T/2} ≡ 0 (mod 3^{2e}).
   With TF's Lemma 4 identities ([x^T]U² = 2H_T/T etc.): g_t ∈ ℤ_(3) and g_t ≡ a²(−1)^t + b² = 4(−1)^t + 1 (mod 3).
10. The mod-3 identity for (2,−1,1) (Lemma J(b)), coefficientwise: ℓ_i ≡ 0 (i odd), ≡ 2 (i even); L_t ≡ t ℓ_t (1/t ≡ t mod 3;
    both 0 when 3 | t); g_t ≡ 0 (t odd), ≡ 2 (t even). For t odd both sides of L_t ≡ [(ψ − 1) g]_t vanish; for t even,
    [(ψ − 1)g]_t = Σ_{i=1}^{t−1} ψ_i g_{t−i} − g_t ≡ (t/2 − 1)·4 − 2 ≡ t/2 ≡ 2t ≡ L_t (mod 3).
Numerics: `numerics/scripts/theoremF_p3_proof_checks.py`, `referee_theoremF_p3.py`, `rereview_theoremF_p3_lemmas.py`.
