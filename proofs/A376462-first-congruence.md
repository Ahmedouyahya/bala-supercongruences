# A376462: proof of the first conjectured supercongruence a(m p^r) ≡ a(m p^(r−1)) (mod p^(3r)), p ≥ 5 (the second congruence is proved in `A376462-shifted-congruence.md`)

**Status.** Machine-checked in Lean 4 + Mathlib together with the shifted congruence (the benchmark statement, both congruences; `verification/lean-checks/A376462/README.md`). Proved: the first of Bala's two conjectured congruences, by the Osburn–Sahu–Straub (OSS) template as in `proofs/A363983.md` (same lemmas; two "singly unscaled" index classes instead of one, each with a self-similar kernel). The second congruence, a(m p^r − 1) ≡ a(m p^{r−1} − 1) (mod p^{3r}), is proved for r = 1 in §5 (via a polynomial-summand representation and first-order harmonic expansions) and for all r ≥ 1 in `proofs/A376462-shifted-congruence.md`, so the "open for r ≥ 2" phrases below are superseded. Conjecture: Peter Bala (OEIS A376462, 2024). Verification: every step below was checked exactly (`numerics/scripts/a376462_oss_steps.py`, `a376462_representations.py`, `a376462_laurent.py`, `a376462_second_r1_steps.py`, `a376462_second_structure.py`; outputs in `numerics/out/`); r = 3 and p ≤ 13 are covered by `numerics/out/a376462_deep_direct_test*.txt` (scripts `a376462_deep_direct_test.py`, `a376462_deep_direct_test2.py`) and p | m by `rereview_oss_a376462.py`; review reports `verification/referee-reports/A376462-proof-first-congruence--nemotron-3-ultra-free.txt`, `verification/referee-reports/A376462-proof-first-congruence--nemotron-3-ultra-free--with-background.txt` and `verification/referee-reports/REREVIEW-A363983-and-A376462-first--fact-only-agent.txt`.

## 0. The sequence and its representations

a(n) = Σ_{k=0}^{n} C(n,k)² C(n+k,k) · A108625(n, n−k),  A108625(n,j) = Σ_i C(n,i)² C(n+j−i, j−i)  (1, 5, 109, 3317, 121501, 4954505, …).

Substituting j = n − k and C(2n−k−i, n−k−i) = C(2n−k−i, n):

    a(n) = Σ_{k=0}^{n} Σ_{i=0}^{n} T(n; k, i),    T(n;k,i) := C(n,k)² C(n+k,k) C(n,i)² C(2n−k−i, n).        (1)

Two further exact forms (checked for n ≤ 11 in `numerics/scripts/a376462_representations.py` and for n ≤ 13 in `numerics/scripts/rereview_oss_a376462.py`): A108625(n, n−k) = Σ_j C(n,j) C(n+j,j) C(n−k, j) (this is the formula T(n,k) = Σ_i C(n,i)C(n+i,i)C(k,i) listed on OEIS A108625; it follows from the Legendre form Σ_i C(n,i)² y^i = (1−y)^n P_n((1+y)/(1−y)) and P_n(1+2y) = Σ_j C(n,j)C(n+j,j) y^j), giving the symmetric form a(n) = Σ_{j,k} C(n,j)C(n−j,k) · C(n,j)C(n+j,j) · C(n,k)C(n+k,k); and, since C(n,j)C(n+j,j) = [u^{−j}] u^{−n}[z^n](1+z)^n(1+u+z)^n, a(n) is the constant term of the n-th power of the Laurent polynomial

    Λ(u,v,z,w) = (1+u+v)(1+z)(1+u+z)(1+w)(1+v+w) / (u v z w),

whose Newton polytope has (0,0,0,0) as its unique interior lattice point (`numerics/out/a376462_laurent.txt`). So a(n) is a constant-term sequence of the kind studied by Samol–van Straten, Mellit–Vlasenko and Beukers–Vlasenko: the Gauss congruences a(mp^r) ≡ a(mp^{r−1}) (mod p^r) hold for constant terms of powers of any integer Laurent polynomial (Beukers–Houben–Straub), the unique-interior-point hypothesis gives the Dwork ratio congruences, and Beukers–Vlasenko (Dwork crystals III, Introduction and Prop. 5.11) obtain p^{2s}-type supercongruences from an excellent Frobenius lift but not p^{3r} in general. We prove p^{3r} directly from (1).

**Theorem.** For every prime p ≥ 5 and m, r ≥ 1: a(m p^r) ≡ a(m p^{r−1}) (mod p^{3r}).

Notation as in `proofs/A363983.md` (and, as there, p ∤ m without loss of generality: the claim for m = p^e m′ is the claim for (m′, r+e) weakened to modulus p^{3r}; runs with p | m, m ∈ {p, 2p}: `numerics/scripts/rereview_oss_a376462.py`, all pass): N = mp^r, M = N/p, Σ' = sum over indices not divisible by p, [x] = floor; Lemmas 1–4 of that note are used verbatim (Kazandzidis quotient form; Σ'_{k<p^s} k^{−2} ≡ 0 (mod p^s); (−1)^kC(mp^r−1,k) ≡ (−1)^{[k/p]}C(mp^{r−1}−1,[k/p]) (mod p^r); C(mp^r+k,k) ≡ C(mp^{r−1}+[k/p],[k/p]) and C(j,mp^r) ≡ C([j/p],mp^{r−1}) (mod p^r)).

## 1. The four classes

Split the index pairs (k,i) of (1) at level N according to divisibility by p: (S) p | k and p | i; (K) p ∤ k, p | i; (I) p | k, p ∤ i; (B) p ∤ k, p ∤ i. Then a(N) − a(M) = [Σ_(S) T(N;k,i) − a(M)] + Σ_(K) + Σ_(I) + Σ_(B).

**Class (B).** For p ∤ k, C(N,k) = (N/k)C(N−1,k−1) has v_p ≥ r, so C(N,k)²C(N,i)² contributes p^{4r}: Σ_(B) ≡ 0 (mod p^{4r}).

**Class (S): scaled terms match the lower level.** Write k = k₁p^s, i = i₁p^σ with p ∤ k₁i₁, s, σ ≥ 1, and K' = k/p, I' = i/p; the pairs with k = 0 (resp. i = 0) are included with the convention s = ∞ (resp. σ = ∞), for which Q_1 = Q_2 = 1 (resp. Q_3 = 1) exactly and everything below goes through verbatim (for k = i = 0, Q_4 = C(2N,N)/C(2M,M) ≡ 1 (mod p^{3r})). Binomials C(a,b) are 0 unless 0 ≤ b ≤ a throughout this note. Then T(N;k,i)/T(M;K',I') = Q_1² Q_2 Q_3² Q_4 with Q_1 = C(N,k)/C(M,K'), Q_2 = C(N+k,k)/C(M+K',K'), Q_3 = C(N,i)/C(M,I'), Q_4 = C(2N−k−i, N)/C(2M−K'−I', M) = C(p(2M−K'−I'), pM)/C(2M−K'−I', M). By Lemma 1 (Kazandzidis), with μ := min(s, σ):
 Q_1 ≡ 1 (mod p^{r+s+min(r,s)}), Q_2 ≡ 1 (mod p^{r+s+min(r,s)}), Q_3 ≡ 1 (mod p^{r+σ+min(r,σ)}), and Q_4 ≡ 1 (mod p^{3+v_p(2M−K'−I')+v_p(M)+v_p(M−K'−I')}) with v_p(2M−K'−I'), v_p(M−K'−I') ≥ min(r−1, μ−1), so Q_4 ≡ 1 (mod p^{r+2+2min(r−1,μ−1)}).
If μ ≥ r every quotient is ≡ 1 (mod p^{3r}) and T(N;k,i) ≡ T(M;K',I') (mod p^{3r}) since T(M;K',I') ∈ ℤ. If μ < r, the product of quotients is ≡ 1 (mod p^{r+2μ}) (each exponent above is ≥ r + 2μ), while v_p(T(M;K',I')) ≥ 2·max(0, r−s) + 2·max(0, r−σ) ≥ 2(r−μ) (from C(M,K')² and C(M,I')², using v_p(C(M,K')) ≥ v_p(M) − v_p(K') ≥ r − s and similarly for I'); hence v_p(T(N;k,i) − T(M;K',I')) ≥ 2(r−μ) + r + 2μ = 3r. The nonvanishing conditions agree at the two levels (k ≤ N ⇔ K' ≤ M, k + i ≤ N ⇔ K' + I' ≤ M), and when K' + I' = M the quotient Q_4 is 1 trivially (Lemma 1 is applied only with lower index strictly between 0 and the upper index). Summing over the bijection (k,i) ↔ (K',I'): Σ_(S) ≡ a(M) (mod p^{3r}).

## 2. Class (K): p ∤ k, p | i

Using C(N,k) = (N/k)C(N−1,k−1): Σ_(K) = N² · S_K with

    S_K := Σ'_k k^{−2} C(N−1,k−1)² C(N+k,k) Σ_{i' } C(N, pi')² C(2N − k − pi', N)   (exact identity, checked).

It suffices to show S_K ≡ 0 (mod p^r). For p ∤ k, [(k−1)/p] = [k/p] and [(2N − k − pi')/p] = 2M − i' − [k/p] − 1; so Lemma 3 (squared, hence without sign), Lemma 4(i), Lemma 1 (C(N,pi') ≡ C(M,i') mod p^{r}) and Lemma 4(ii) give, modulo p^r,

    S_K ≡ Σ'_k k^{−2} Ψ_1(M, [k/p]),    Ψ_1(M', n') := C(M'−1,n')² C(M'+n',n') Σ_{i'} C(M',i')² C(2M' − n' − 1 − i', M').

**Lemma 7 (self-similarity).** For t ≥ 1 and all n' ≥ 0: Ψ_1(mp^t, n') ≡ Ψ_1(mp^{t−1}, [n'/p]) (mod p^t).
Proof. C(mp^t−1,n')² ≡ C(mp^{t−1}−1,[n'/p])² and C(mp^t+n',n') ≡ C(mp^{t−1}+[n'/p],[n'/p]) (Lemmas 3, 4(i)). In the inner sum, terms with p ∤ i' carry C(mp^t,i')² ≡ 0 (mod p^{2t}); for i' = pi'', C(mp^t,pi'')² ≡ C(mp^{t−1},i'')² (Lemma 1) and C(2mp^t − n' − 1 − pi'', mp^t) ≡ C([(2mp^t − n' − 1 − pi'')/p], mp^{t−1}) = C(2mp^{t−1} − i'' − [n'/p] − 1, mp^{t−1}) (Lemma 4(ii), using ⌈(n'+1)/p⌉ = [n'/p] + 1). ∎ (Checked exhaustively for p ∈ {5,7}, t ≤ 2, m ≤ 2, all n' < 2mp^t+2: 532 cases, no failure; likewise for Ψ_2 below.)

Define Σ_s := Σ'_{1≤k≤N} k^{−2} Ψ_1(mp^{r−s}, [k/p^s]) for s = 1, …, r. Grouping the k with [k/p^s] = n (complete blocks of length p^s, since p^s | N), Σ_s = Σ_n Ψ_1(mp^{r−s}, n) · Σ'_{[k/p^s]=n} k^{−2}, and each inner sum is ≡ Σ'_{u<p^s} u^{−2} ≡ 0 (mod p^s) (Lemma 2). For s < r, Lemma 7 (with t = r − s) lets us replace Ψ_1(mp^{r−s}, n) by Ψ_1(mp^{r−s−1}, [n/p]) at the cost of p^{r−s}·p^s = p^r, which turns Σ_s into Σ_{s+1}; for s = r the inner sums are ≡ 0 (mod p^r) outright. Hence S_K ≡ Σ_1 ≡ … ≡ Σ_r ≡ 0 (mod p^r), and Σ_(K) ≡ 0 (mod p^{3r}).

## 3. Class (I): p | k, p ∤ i

Symmetrically, Σ_(I) = N² S_I with S_I := Σ'_i i^{−2} C(N−1,i−1)² Σ_{k'} C(N,pk')² C(N+pk',pk') C(2N − pk' − i, N) ≡ Σ'_i i^{−2} Ψ_2(M,[i/p]) (mod p^r), where Ψ_2(M',n') := C(M'−1,n')² Σ_{k'} C(M',k')² C(M'+k',k') C(2M' − k' − n' − 1, M'), and Ψ_2(mp^t, n') ≡ Ψ_2(mp^{t−1}, [n'/p]) (mod p^t) by the same lemmas (now C(mp^t+pk'',pk'') ≡ C(mp^{t−1}+k'',k'') is Lemma 1). The same induction gives S_I ≡ 0 (mod p^r), so Σ_(I) ≡ 0 (mod p^{3r}).

Combining §1–§3: a(N) − a(M) ≡ 0 (mod p^{3r}). ∎

## 4. Computer verification of each step (`numerics/out/a376462_oss_steps.txt`, p ∈ {5,7}, r ≤ 2, m ≤ 2)
Scaled class: termwise and summed slack ≥ 0 (min 0). Classes K, I, B: slack ≥ 0. Exact identities Σ_(K) = N²S_K and Σ_(I) = N²S_I: True. Reductions S_K ≡ Σ_1 and S_I ≡ Σ_1 (mod p^r): slack ≥ 0. Chains Σ_s ≡ Σ_{s+1} and Σ_r ≡ 0 (mod p^r): slack ≥ 0 (min 0 attained on the I side and for Σ_r, so those steps are tight; S_K ≡ Σ_1, the K-chain and Lemma 7 for Ψ_1 have slack ≥ 1 in all runs, `numerics/out/rereview_oss_a376462.txt`). Self-similarity of Ψ_1, Ψ_2: no failures. Theorem: v_p(a(mp^r) − a(mp^{r−1})) − 3r ∈ {0, 1} for p ∈ {5, 7, 11}, m ≤ 2, r ≤ 2 (`sweep_2026-10-15.py`).

## 5. The second congruence: proved for r = 1 (superseded: all r ≥ 1 are proved in `proofs/A376462-shifted-congruence.md`)

Note added 2026-10-15 (night). The first-order expansions used below (C(N−1,k)² ≡ C(m−1,n')²(1 − 2pmH'_k) etc.) are the r = 1 case of the exact product expansions of Lemma 1.3 of the shifted-congruence note, where they are proved for every r; this section is kept as the original r = 1 argument and as a worked example, and is no longer needed for the theorem.

**Representation.** With j := n − k − i (so C(2n−k−i,n) = C(n+j,j)) the summand becomes a polynomial in n for fixed (k,j): a(n) = Σ_{k,j≥0} S(n;k,j), S(n;k,j) = C(n,k)²C(n+k,k)C(n,k+j)²C(n+j,j). Writing the argument as N − 1 (N ≥ 1) this reads

    a(N−1) = Σ_{k,j ≥ 0, k+j ≤ N−1} S̃(N;k,j),   S̃(N;k,j) := S(N−1;k,j) = C(N−1,k)² C(N+k−1,k) C(N−1,k+j)² C(N+j−1,j)        (checked exactly for N ≤ 13 in `numerics/scripts/a376462_second_structure.py` and for N ≤ 20 in `numerics/scripts/rereview_oss_a376462.py`).

This is only a re-indexing of (1); its value is that each factor now has one of the shapes C(N−1,·), C(N+·−1,·) that Lemmas 3–4 and Kazandzidis handle. (For comparison: for the Apéry numbers A(−n) = A(n−1), which makes the shifted congruence a special case of the unshifted one at negative arguments, Straub 2014, Remark 1.3. No such identity holds here: with the dual kernel S*(n;k,j) := C(n+k,k)²C(n,k)C(n+k+j,k+j)²C(n,j) one has S*(−N;k,j) = (−1)^{k+j}S̃(N;k,j), and Σ_{k,j}S*(−N;k,j) = 1, −3, −11, 1077, … ≠ a(N−1).)

**Proposition (r = 1).** For p ≥ 5 and m ≥ 1: a(mp − 1) ≡ a(m − 1) (mod p³).

Proof. N = mp, M = m. Split the pairs (k,j) by divisibility by p into (S) p | k, p | j; (K) p ∤ k, p | j; (J) p | k, p ∤ j; (B) p ∤ k, p ∤ j. Write H'_k := Σ_{p∤i≤k} 1/i.
(S) For k = pk', j = pj' with k' + j' ≤ M − 1 (so M − k' ≥ 1 and M − k' − j' ≥ 1, and the pairs biject with the index set of a(M−1), since pk' + pj' ≤ N − 1 ⇔ k' + j' ≤ M − 1): C(N−1,pk')/C(M−1,k') = C(pM,pk')/C(M,k') (because C(X−1,Y) = ((X−Y)/X)C(X,Y) and the factor (M−k')/M is common to both levels), C(N+pk'−1,pk')/C(M+k'−1,k') = C(p(M+k'),pk')/C(M+k',k'), and likewise for the two j-factors; each quotient is ≡ 1 (mod p³) by Kazandzidis (Lemma 1; it equals 1 when k' = 0 or j' = 0), so S̃(N;pk',pj') ≡ S̃(M;k',j') (mod p³) termwise.
(B) C(N+k−1,k) = (N/k)C(N+k−1,k−1) and C(N+j−1,j) = (N/j)C(N+j−1,j−1) give a factor N²/(kj) = p²m²/(kj); modulo p the remaining factor R(k,j) := C(N−1,k)²C(N+k−1,k−1)C(N−1,k+j)²C(N+j−1,j−1) depends, by Lucas' theorem, only on ([k/p], [j/p]) and on δ := [k mod p + j mod p ≥ p] (through C(N−1,k+j)² ≡ C(M−1,[k/p]+[j/p]+δ)²). Hence Σ_(B) ≡ p²m² Σ_{blocks} [R_0 Σ_{u+v<p} 1/(uv) + R_1 Σ_{u+v≥p} 1/(uv)] (mod p³) with u, v ranging over 1..p−1 (1/(n'p+u) ≡ 1/u mod p; the Lucas signs C(p−1,u) ≡ (−1)^u disappear in the squares; completing the top blocks to full (u,v)-squares adds only pairs with k + j ≥ mp > N − 1, where S̃ = 0 and R_1 = 0 because C(m−1,m) = 0), and both double sums vanish mod p: Σ_{u+v<p} 1/(uv) = Σ_{n=2}^{p−1} (2/n)H_{n−1} = H_{p−1}² − H^{(2)}_{p−1} ≡ 0 and Σ_{u+v≥p} 1/(uv) = H_{p−1}² − Σ_{u+v<p} ≡ 0 (mod p), using H_{p−1} ≡ 0 (mod p²), H^{(2)}_{p−1} ≡ 0 (mod p) for p ≥ 5. So Σ_(B) ≡ 0 (mod p³).
(K) Σ_(K) = N · Σ'_k (1/k) B(k), B(k) := C(N−1,k)² C(N+k−1,k−1) Σ_{j'} C(N−1,k+pj')² C(N+pj'−1,pj'). First-order expansions modulo p², for p ∤ k, n' := [k/p] (from the product formulas behind Lemma 3 and Lemma 4(i), keeping the first-order term, and Kazandzidis for the last factor; all verified exactly for p ∈ {5,7,11}, m ≤ 3):
  C(N−1,k)² ≡ C(m−1,n')² (1 − 2pm H'_k),   C(N+k−1,k−1) ≡ C(m+n',n') (1 + pm(H'_k − 1/k)),
  C(N−1,k+pj')² ≡ C(m−1,n'+j')² (1 − 2pm H'_k)  (since H'_{k+pj'} ≡ H'_k mod p),   C(N+pj'−1,pj') ≡ C(m+j'−1,j').
Hence B(k) ≡ B_0(n') (1 − 3pm H'_k − pm/k) (mod p²) with B_0(n') := C(m−1,n')²C(m+n',n')Σ_{j'}C(m−1,n'+j')²C(m+j'−1,j'), and
  Σ'_k B(k)/k ≡ Σ_{n'} B_0(n') · Σ'_{[k/p]=n'} [ 1/k − 3pm H'_k/k − pm/k² ]  (mod p²).
Each block sum vanishes: Σ'_{block} 1/k ≡ Σ_u 1/u − n'p Σ_u 1/u² ≡ 0 (mod p²); Σ'_{block} 1/k² ≡ Σ_u 1/u² ≡ 0 (mod p); and Σ'_{block} H'_k/k ≡ Σ_{u=1}^{p−1} H_u/u = (H_{p−1}² + H^{(2)}_{p−1})/2 ≡ 0 (mod p), because H'_{n'p+u} ≡ H'_{n'p} + H_u and H'_{n'p} ≡ 0 (mod p). Therefore Σ'_k B(k)/k ≡ 0 (mod p²) and Σ_(K) ≡ 0 (mod p³).
(J) Σ_(J) = N · Σ'_j (1/j) B̃(j) with B̃(j) := C(N+j−1,j−1) Σ_{k'} C(N−1,pk')² C(N+pk'−1,pk') C(N−1,pk'+j)². The k'-factors are Kazandzidis-exact: C(N−1,pk')² ≡ C(m−1,k')², C(N+pk'−1,pk') ≡ C(m+k'−1,k') (mod p³). Only two factors depend on j: C(N−1,pk'+j)² ≡ C(m−1,k'+[j/p])²(1 − 2pmH'_j) and C(N+j−1,j−1) ≡ C(m+[j/p],[j/p])(1 + pm(H'_j − 1/j)) (mod p²), so B̃(j) ≡ B̃_0([j/p])(1 − pmH'_j − pm/j) with B̃_0(n'') := C(m+n'',n'')Σ_{k'}C(m−1,k')²C(m+k'−1,k')C(m−1,k'+n'')² (the H'-coefficient is −1 here, against −3 in (K), because C(N−1,k)² is replaced by the j-independent C(N−1,pk')²); the same block sums give Σ'_j B̃(j)/j ≡ 0 (mod p²) and Σ_(J) ≡ 0 (mod p³). ∎
Numerics (`numerics/out/a376462_second_r1_steps.txt`; the independent re-check `numerics/scripts/rereview_oss_a376462.py` verified every sub-claim of this section for p ∈ {5,7,11,13}, m ∈ {1,…,6, p, p+1}, and the Proposition for p ≤ 23, m ≤ 6, including p | m, 0 failures): every displayed sub-claim verified exactly (block sums, expansions, double harmonic sums), and the three classes vanish mod p³ for p ∈ {5,7,11,13}, m ≤ 4 (slack 0 or 1). For r ≥ 2 the data (`a376462_second_structure.txt`) show that all four classes still vanish mod p^{3r} individually, but now even the scaled pairs match only in the aggregate (termwise deficit −1 at r = 2), so a proof needs expansions to order p^{2r} with Wolstenholme-type sums over blocks of length p^s (Coster-type analysis). Open at the time of writing; now closed by the shifted-congruence note.

**Remark (literature).** Straub (2014) observes that among the classical Apéry-like sequences only A005258 and A005259 satisfy shifted supercongruences, and explains them through negative multi-indices of a multivariate rational function (his Theorem 1.2/3.2). A376462 is a MacMahon-type coefficient: a(n) = [ (tuvzw)^n ] (t+u+v)^n(t+z)^n(t+u+z)^n(t+w)^n(t+v+w)^n (homogenise the 1's of Λ to a fifth variable; the extra variable's exponent is forced by homogeneity; checked for n ≤ 4), hence a(n) is the diagonal coefficient of 1/det(I − A·diag(t,u,v,z,w)) for the 5×5 coefficient matrix A of these forms. However, for none of the 120 assignments of forms to variables does this determinant have Straub's block shape Π_j(1 − Σ_{block j} x_i) − ε·tuvzw (all 120 distinct determinants were computed (`numerics/out/a376462_straub_shape_search.txt`; no factoring step)), so A376462 is *not* an instance of Straub's family A_{λ,ε} and his Theorem 3.2 cannot be cited; his method (Gessel–Beukers style, uniform in negative indices) may still adapt, which is the natural route to r ≥ 2. A 4-variable multivariate extension of a(n) with negative entries does satisfy A(pn; pd) ≡ A(n; d) (mod p³) in random tests (`numerics/scripts/a376462_multivariate.py`), consistent with such a theorem.

## References
- R. Osburn, B. Sahu, A. Straub, Supercongruences for sporadic sequences, Proc. Edinb. Math. Soc. 59 (2016), arXiv:1312.2195.
- A. Robert, M. Zuber, The Kazandzidis supercongruences, Rend. Sem. Mat. Padova 94 (1995).
- F. Beukers, M. Vlasenko, Dwork crystals III, arXiv:2105.14841; A. Mellit, M. Vlasenko, Dwork's congruences for the constant terms of powers of a Laurent polynomial, arXiv:1306.5811; A. Straub, Multivariate Apéry numbers and supercongruences of rational functions, arXiv:1401.0854.
- P. Bala, OEIS A376462 (2024), A108625 (2008 comments).
