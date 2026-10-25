# Theorem F: the cubic tower for [x^{cN}] ((1+x)^a (1−x)^b)^N, with proofs of Bala's conjectures on A333561, A333562, A119259, A352373, and of the p ≥ 5 part of the conjecture on A333565

**Status.** Proved (elementary, self-contained) and machine-checked in Lean 4 + Mathlib for all integers a, b and c ≥ 0 (`TF.theoremF`, with A(N) defined through the power-series exponential; the instances A333561, A333562, A352373 and A333565 as benchmark statements; `verification/lean-checks/TheoremF-A333561-A333562-A352373/README.md`). The case c = a (and, by x → −x, c = b) is a special case of Straub, Algebra & Number Theory 8 (2014), Theorem 3.2(b); the four OEIS instances have c ∉ {a, b}. Bala's general conjectures on A352373 (c = 1, all r, s) and A333715 ((a, b, c) = (s, −s, r)) are machine-checked corollaries for p ≥ 5 (`verification/lean-checks/BalaGeneral/`). Earlier claim: the same theorem for p ≥ 5, with modulus 3^(3r−1) at p = 3, and with it the conjectures on A333561 (as the case c = 2, not named there), A333562, A333565 (for p ≥ 5) and A352373, was claimed before this work in rbajaj5's unreviewed drafts `CoefficientFramingCubicTower.md` (first posted 2026-07-30) and `BalaAugustCoefficientPacket.md` (2026-08-11), with no machine check; see `literature/PRIOR-CLAIMS.md`. This note is our own complete derivation, written after reading those drafts; the overall strategy (reduced logarithm, quadratic estimate) is the same as theirs and as in the Epoch A333096 proof; every lemma below is proved here. Conjectures: Peter Bala (OEIS, 2015–2022). Verification: Lemmas 3, 6 and the Theorem are tested in `numerics/scripts/theoremF_framing_tests.py` (all bounds attained, i.e. tight), including a term-by-term check at r = 3 (p = 5) where the Lemma 6 branch with τ ≥ 1 is exercised (`rereview_theoremF_p5_valuations.py`); further `rereview_theoremF_p5_identities.py`, `rereview_theoremF_oeis_extra.py`, `theoremF_deep_direct_sweep.py` and `theoremF_deep_direct_sweep2.py` (outputs in `numerics/out/`); review reports `verification/referee-reports/TheoremF-coefficient-framing-proof--nemotron-3-ultra-free.txt` and `verification/referee-reports/REREVIEW-TheoremF-and-TheoremF-p3--fact-only-agent.txt`.

## 0. Statement

Fix a prime p ≥ 5, integers a, b (any signs) and c ≥ 0. Put φ(x) = (1+x)^a (1−x)^b ∈ ℤ[[x]] and A(N) := [x^{cN}] φ(x)^N.

**Theorem F.** For every M ≥ 1, with r := 1 + v_p(M):  A(pM) ≡ A(M) (mod p^{3r}). Equivalently A(np^r) ≡ A(np^{r−1}) (mod p^{3r}) for all n, r ≥ 1.

(For c = 0 one has A(N) = [x^0]φ^N = 1 for every N and there is nothing to prove; in the proof below c ≥ 1 is assumed, so that the sums in §4 are non-empty.)

Instances (identities proved in §5): A333561 = A with (a,b,c) = (3,−1,2); A333562: (4,−1,3); A119259: (2,−1,1); A352373: (−1,−3,1); A103885: (1,−1,2); A333565(n) = 2·A(2,−1,1)(n) − (−1)^n. Since (−1)^{np^r} = (−1)^{np^{r−1}} for odd p, Bala's p ≥ 5 conjectures on A333561, A333562, A119259 and A352373 are settled, and so is the p ≥ 5 part of the conjecture on A333565 (Bala conjectured p ≥ 3 there; the p = 3 case is proved separately in `proofs/TheoremF-p-eq-3.md`). A103885 and A002003 carry no tower conjecture on the OEIS (only a(p) ≡ 2 mod p³); the cubic tower for them is a by-product.

Sharpness: v_p(A(np^r) − A(np^{r−1})) = 3r exactly in most tested cases (`numerics/out/theoremF_framing_tests.txt`); for A352373 at p = 3 the valuation is 3r − 1 whenever n ≡ 1 (mod 3) (e.g. n = 1, 4, 7; for n ≡ 2 (mod 3) it is ≥ 3r; `numerics/out/theoremF_p3_sweep.txt`, `numerics/out/rereview_theoremF_p3_lemmas.txt`), so p ≥ 5 cannot be dropped in general.

## 1. The reduced logarithm

For p ∤ j write U := Σ_{j≥1, p∤j} x^j/j and V := Σ_{j≥1, p∤j} (−1)^{j+1} x^j/j (both in ℤ_(p)[[x]], with no monomial x^T, p | T).

**Lemma 1.** φ(x)^p = φ(x^p) · exp(p L(x)) in ℚ[[x]], where L := aV − bU.
Proof. p log(1+x) − log(1+x^p) = Σ_j (−1)^{j+1} p x^j/j − Σ_i (−1)^{i+1} x^{pi}/i; the terms j = pi of the first sum equal (−1)^{pi+1} x^{pi}/i = (−1)^{i+1}x^{pi}/i (p odd) and cancel the second sum, leaving pV. Likewise p log(1−x) − log(1−x^p) = −pU. Multiply by a, b and exponentiate (all series have zero constant term, so exp and log are inverse bijections between 1 + xℚ[[x]] and xℚ[[x]]). ∎

## 2. Harmonic sums over units (p ≥ 5)

For T ≥ 1 let H_T := Σ_{0<i<T, p∤i} 1/i and H_T^± := Σ_{0<i<T, p∤i} (−1)^{i+1}/i. For e ≥ 1 let R_e := {u : 0 < u < p^e, p ∤ u} and S_j := Σ_{u∈R_e} u^{−j}.

**Lemma 2 (classical).** For p ≥ 5 and e ≥ 1: S_2 ≡ 0 (mod p^e) and S_1 ≡ 0 (mod p^{2e}).
Proof. u ↦ u^{−1} permutes R_e modulo p^e, so S_2 ≡ Σ_{u∈R_e} u² = Σ_{v=1}^{p^e−1} v² − p² Σ_{w=1}^{p^{e−1}−1} w² = (p^e−1)p^e(2p^e−1)/6 − p²(p^{e−1}−1)p^{e−1}(2p^{e−1}−1)/6 ≡ 0 (mod p^e) since 6 is a unit. Pairing u with p^e − u: 1/u + 1/(p^e−u) = p^e/(u(p^e−u)) ≡ −p^e u^{−2} (mod p^{2e}) (because 1/(p^e − u) ≡ −1/u (mod p^e)), hence 2S_1 ≡ −p^e S_2 ≡ 0 (mod p^{2e}). ∎

**Lemma 3.** Let T ≡ 0 (mod p), e := v_p(T) ≥ 1. Then (i) H_T ≡ 0 (mod p^{2e}); (ii) if T is even, H_T^± ≡ 0 (mod p^{2e}).
Proof. Write T = ℓ p^e and i = β p^e + u with 0 ≤ β < ℓ, u ∈ R_e (ℓ, β are local names, unrelated to the parameters a, b, c). (i) (βp^e + u)^{−1} = u^{−1} − βp^e u^{−1}(βp^e+u)^{−1}, and the second term is ≡ −βp^e u^{−2} (mod p^{2e}); so Σ_u (βp^e+u)^{−1} ≡ S_1 − βp^e S_2 ≡ 0 (mod p^{2e}) by Lemma 2; sum over β. (ii) Since p^e is odd, (−1)^{βp^e+u+1} = (−1)^β(−1)^{u+1}, so H_T^± ≡ Σ_{β<ℓ} (−1)^β (S_1^± − βp^e S_2^±) (mod p^{2e}) with S_j^± := Σ_{u∈R_e}(−1)^{u+1}u^{−j}. T even and p^e odd force ℓ even, so Σ_{β<ℓ}(−1)^β = 0 and Σ_{β<ℓ}(−1)^β β = −ℓ/2 ∈ ℤ (this cancellation is essential: v_p(S_1^±) = 0 in the data); it remains to see S_2^± ≡ 0 (mod p^e): the even u ∈ R_e are u = 2v with v ∈ R_e, v < p^e/2, and Σ_{v<p^e/2, p∤v} v^{−2} ≡ ½ S_2 ≡ 0 (mod p^e) (pair v ↔ p^e − v), so Σ_{u even} u^{−2} = ¼ Σ_v v^{−2} ≡ 0 and Σ_{u odd} u^{−2} = S_2 − Σ_{u even} ≡ 0; hence S_2^± = Σ_{odd} − Σ_{even} ≡ 0 (mod p^e). ∎

**Lemma 4 (coefficients of L²).** For T ≡ 0 (mod p): [x^T]U² = 2H_T/T, [x^T]V² = (−1)^T 2H_T/T, [x^T]UV = (1 + (−1)^T) H_T^±/T (for odd T both sides vanish, so no sign factor is needed there). Consequently v_p([x^T] L²) ≥ v_p(T) for p ≥ 5.
Proof. [x^T]U² = Σ_{i+j=T, p∤i, p∤j} 1/(ij) = (1/T) Σ (1/i + 1/j) = (2/T) Σ_{0<i<T, p∤i} 1/i (p | T makes p ∤ i ⇔ p ∤ T−i). The other two are identical computations with the signs (−1)^{i+1}(−1)^{j+1} = (−1)^T and (−1)^{j+1} = (−1)^T(−1)^{i+1}. The last claim: by Lemma 3 each of H_T, (1+(−1)^T)H_T^± is divisible by p^{2e} (the cross term vanishes for odd T), and v_p(1/T) = −e. ∎

## 3. Frobenius lifting

**Lemma 5.** Let f ∈ ℤ[[y]], k ≥ t ≥ 0. Then f(y)^{p^k} ≡ f(y^{p^t})^{p^{k−t}} (mod p^{k−t+1}) coefficientwise.
Proof. f(y)^p ≡ f(y^p) (mod p) (freshman's dream), so f(y)^{p^t} ≡ f(y^{p^t}) (mod p) by induction; and X ≡ Y (mod p) implies X^{p^u} ≡ Y^{p^u} (mod p^{u+1}) in ℤ[[y]] (induction on u using X^p − Y^p = (X−Y)(X^{p−1} + … + Y^{p−1}) and X^{p−1}+…+Y^{p−1} ≡ pX^{p−1} ≡ 0 (mod p) when X ≡ Y). Take u = k − t. ∎

**Lemma 6.** Let M = p^{r−1} m with p ∤ m, φ(y)^M = Σ_s γ_s y^s. If s ≥ 1 and σ := v_p(s) ≤ r − 2, then v_p(γ_s) ≥ r − 1 − σ.
Proof. Lemma 5 with k = r−1, t = σ+1 ≤ k gives φ^{p^{r−1}} ≡ Ψ(y^{p^{σ+1}}) (mod p^{r−1−σ}) for some Ψ ∈ ℤ[[y]], hence φ^M = (φ^{p^{r−1}})^m ≡ Ψ(y^{p^{σ+1}})^m (mod p^{r−1−σ}); the right side has no monomial y^s with p^{σ+1} ∤ s. ∎

## 4. Proof of Theorem F

Let N = pM, r = 1 + v_p(M). By Lemma 1, (φ(x)/x^c)^N = (φ(x)^p/x^{pc})^M = (φ(x^p)/x^{pc})^M · exp(N L(x)). Taking [x^0] and using [x^0](φ(x^p)/x^{pc})^M = [y^{cM}]φ(y)^M = A(M):

    A(N) − A(M) = [x^0] ( (φ(x^p)/x^{pc})^M · (exp(NL(x)) − 1) ) = Σ_{s=0}^{cM−1} γ_s · ε_{p(cM−s)},        (1)

where exp(NL) − 1 = Σ_{T≥1} ε_T x^T and (φ(x^p)/x^{pc})^M = Σ_s γ_s x^{p(s−cM)} (only s < cM meet a positive T). Every sum is finite.

Coefficients ε_T for T = pT' (T' ≥ 1): ε_T = Σ_{j=1}^{T} (N^j/j!) [x^T]L^j.
 • j = 1: [x^T]L = 0 (L has no monomial with exponent divisible by p).
 • j = 2: v_p(N²[x^T]L²/2) ≥ 2r + v_p(T) by Lemma 4 (v_p(N) = r).
 • j ≥ 3: [x^T]L^j ∈ ℤ_(p) and v_p(N^j/j!) = jr − v_p(j!) ≥ 3r, because v_p(j!) ≤ (j−1)/(p−1) ≤ (j−1)/4 ≤ (j−3)r for j ≥ 4 (and v_p(3!) = 0 for p ≥ 5).
Hence v_p(ε_T) ≥ min(2r + v_p(T), 3r) for every T ≡ 0 (mod p).                                   (2)

Now fix s in (1) and put τ := v_p(cM − s), so v_p(T) = 1 + τ. If τ ≥ r − 1, (2) gives v_p(ε_T) ≥ 3r. If τ ≤ r − 2, then since v_p(cM) ≥ v_p(M) = r − 1 > τ we must have σ := v_p(s) = τ ≤ r − 2 (s ≥ 1), so Lemma 6 gives v_p(γ_s) ≥ r − 1 − τ and (2) gives v_p(ε_T) ≥ 2r + 1 + τ; the product has valuation ≥ 3r. Therefore every term of (1) is divisible by p^{3r}. ∎

(Where p ≥ 5 was used: Lemma 2 needs 6 invertible, Lemma 3(ii) needs 2 invertible, the j = 3 term needs p ∤ 3!. For p = 3, Lemma 2 fails by exactly one power (v_3(S_2) = e − 1, v_3(S_1) = 2e − 1 in the data); the weakened bounds give 3^{3r−1}, which is Theorem F₃(i) of `proofs/TheoremF-p-eq-3.md`.)

## 5. The instances

(a) A333561, A333562, A119259. For c ≥ 1 let S_c(n) := Σ_{j=0}^{cn} 2^j C(n+j−1, j) (c = 1: A119259 by P. Barry's formula on the entry; c = 2: A333561; c = 3: A333562). Since Σ_j C(n+j−1,j)2^j x^j = (1−2x)^{−n}, S_c(n) = [x^{cn}] (1−x)^{−1}(1−2x)^{−n}. Substituting x = z/(1+z) (so 1 − x = 1/(1+z), 1 − 2x = (1−z)/(1+z)) and using [x^K] f(x) = [z^K] f(z/(1+z)) (1+z)^{K−1} (the change-of-variables formula [x^K]f = [z^K] f(x(z)) ψ(z)^K (1 − zψ'(z)/ψ(z)) for x = z/ψ(z), here ψ = 1+z):

    S_c(n) = [z^{cn}] (1+z)^{n+1}(1−z)^{−n}(1+z)^{cn−1} = [z^{cn}] (1+z)^{(c+1)n}(1−z)^{−n} = A_{(c+1, −1, c)}(n).

(Checked exactly for n ≤ 12, c = 2, 3 in `numerics/scripts/theoremF_framing_tests.py`, and for c ≤ 5, n ≤ 25 in `numerics/scripts/rereview_theoremF_p5_identities.py`.)
(b) A352373: a(n) = [x^n] (1/((1−x)²(1−x²)))^n = [x^n] ((1+x)^{−1}(1−x)^{−3})^n = A_{(−1,−3,1)}(n) by definition (1 − x² = (1−x)(1+x)).
(c) A333565. Let B(n) := A_{(2,−1,1)}(n) = [x^n]((1+x)²/(1−x))^n (= A119259(n) by Bala's formula on that entry). With x = x(t) the power-series solution of x = t(1+x)²/(1−x), i.e. x = ((1−2t) − √(1−8t))/(2(1+t)), the Lagrange-inversion identity Σ_N t^N [x^N]φ(x)^N = 1/(1 − tφ'(x(t))) = φ/(φ − xφ') gives Σ_N B(N)t^N = (1−x²)/(1−3x). A direct symbolic simplification (sympy) shows 2(1−x²)/(1−3x) − 1/(1+t) = (1+4t)/((1+t)√(1−8t)), the o.g.f. defining A333565; hence A333565(n) = 2B(n) − (−1)^n for all n ≥ 0 (also checked termwise for n ≤ 12).
(d) A103885(n) = [x^{2n}]((1+x)/(1−x))^n = A_{(1,−1,2)}(n) by its OEIS definition. For A002003 the coefficient form [x^n]((1+x)/(1−x))^n is a formula on the entry (verified against the OEIS b-file for 1 ≤ n ≤ 45 in `numerics/scripts/rereview_theoremF_oeis_extra.py`, not proved here; it fails at n = 0 where A002003(0) = 0). A333564 = (A119259 − (−1)^n)/2 is an OEIS formula; the sympy computation in (c) proves the equivalent statement for A333565 (the relation A333565 = 2·A119259 − (−1)^n is also an %F line on the entry).

## 6. Remarks
- For p = 3: the cubic tower is now **proved** in `proofs/TheoremF-p-eq-3.md` (Theorem F₃) whenever 3 | c, or a + b ≡ c (mod 3), or a ≡ b ≡ 0 (mod 3), which covers A119259, A333561, A333562, A333565 and A333564; in all other classes the proof gives 3^{3r−1}, and the data show that exponent is attained for suitable n (in the class a ≡ b ≡ 0 the observed valuation is ≥ 3r + 1). Correction (2026-10-15, night): an earlier version of this paragraph listed A002003 among the sequences satisfying the p = 3 tower; that was wrong — A002003 = A_{(1,−1,1)} has a + b = 0 ≢ 1 and v_3(a(3) − a(1)) = v_3(36) = 2 (`numerics/out/theoremF_p3_sweep.txt`). The earlier measurements (E₂ and E₃ each of valuation 3r − 1, cancelling only in aggregate) are explained by Proposition I of the p = 3 note.
- Theorem F with b = 0 is the Jacobsthal–Kazandzidis congruence C(anp^r, cnp^r) ≡ C(anp^{r−1}, cnp^{r−1}) (mod p^{3r}), a consistency check (also tested: slack 0 for C(2N,N)).
- The same proof works for φ = Π_i (1 + ε_i x^{u_i})^{a_i} as long as the quadratic coefficient estimate (Lemma 4) holds for the resulting L; for u_i > 1 the relevant sums are harmonic sums restricted to residue classes, which in general are only divisible by p^{e}, giving quadratic towers (cf. A386548 and A246437, exponent 2r).

## 7. Computer checks
`numerics/scripts/theoremF_framing_tests.py` (output in `numerics/out/`): Lemma 3 bounds (min slack 0 over T ≤ 60p, p ∈ {5,7,11,13}); Lemma 6 (min slack 0 over several (a,b), r ≤ 3); Theorem F for ten (a,b,c) triples × p ∈ {5,7,11,13} × r ≤ 2 × n ≤ 2 (all slack ≥ 0, min 0); instance identities. Independent re-check scripts `numerics/scripts/rereview_theoremF_p5_identities.py` (129 checks: Lemmas 1, 4, 5, identity (1), change of variables, §5 identities with sympy, OEIS data) and `numerics/scripts/rereview_theoremF_p5_valuations.py` (144 checks: Lemmas 2, 3, 6, the ε_T estimate, Theorem F for 18 triples × p ∈ {5,7,11,13} × r ≤ 3, term-by-term (1) at p = 5, r ≤ 3): 0 failures.

## References
- P. Bala, OEIS A333561, A333562, A333565, A119259 (formulas and conjectures), A352373, A103885, A002003.
- T. Adamczewski, OEIS Open, arXiv:2608.11941, App. A (the reduced-logarithm/Cartier strategy in the A333096 proof).
- rbajaj5, `CoefficientFramingCubicTower.md`, `BalaAugustCoefficientPacket.md` (unreviewed drafts, Aug 2026, in the repository `rbajaj5/a183068-supercongruence`; same strategy; not included here, see `literature/README.md`).
- R. Meštrović, arXiv:1111.3057 (Wolstenholme-type sums over units modulo prime powers).
