# Theorem F at p = 3: the cubic tower for [x^{cN}] ((1+x)^a (1−x)^b)^N when 3 | c or a + b ≡ c (mod 3) — completing Bala's "p ≥ 3" conjecture on A333565 (and A333564, A119259, A333561, A333562)

**Status.** Proved (elementary, self-contained). Machine-checked in Lean 4 + Mathlib for the instance (a, b, c) = (2, −1, 1) only, which gives A333565 at p = 3 (`verification/lean-checks/A333565/README.md`); the other instances, including A333561 and A333562 at p = 3, are written proofs only. Method: the reduced-logarithm set-up of `proofs/TheoremF-p-ge-5.md` (there p ≥ 5), plus two new ingredients at p = 3: (1) an exact "exact-form" identity for the coefficient functional (Lemma A), which converts the quadratic term into a term of the same shape as the cubic one; (2) an identity in F_3[[y]] (Lemma J) showing that the resulting mod-3 obstruction is a multiple of ψ − c, which the functional kills. Earlier claim: the uniform bound 3^(3r−1) for all (a, b, c) was claimed before this work in rbajaj5's unreviewed draft `CoefficientFramingCubicTower.md` (2026-07-30); the classification of the classes in which the 3^(3r) tower holds, and with it Bala's case p = 3 of A333565, is not claimed there (`literature/PRIOR-CLAIMS.md`). Conjectures: Peter Bala (OEIS). Verification: every step re-checked numerically in `numerics/scripts/theoremF_p3_proof_checks.py` (output `numerics/out/theoremF_p3_proof_checks.txt`) and independently, with separate code, in `numerics/scripts/referee_theoremF_p3.py` (0 failing checks); further `theoremF_p3_conjecture_check.py`, `theoremF_p3_sweep.py`, `rereview_theoremF_p3_lemmas.py`, `theoremF_deep_direct_sweep.py` and `theoremF_deep_direct_sweep2.py` (outputs in `numerics/out/`); review reports `verification/referee-reports/TheoremF-p3-proof--nemotron-3-ultra-free.txt`, `verification/referee-reports/TheoremF-p3-proof--deepseek-v4.1-flash-free.txt` and `verification/referee-reports/REREVIEW-TheoremF-and-TheoremF-p3--fact-only-agent.txt`.

## 0. Statement

Fix integers a, b and c ≥ 1. Put φ(x) = (1+x)^a (1−x)^b ∈ ℤ[[x]] and A(N) := [x^{cN}] φ(x)^N. For M ≥ 1 write r := 1 + v_3(M) and N := 3M.

**Theorem F₃.**
(i) For all a, b, c: A(3M) ≡ A(M) (mod 3^{3r−1}).
(ii) If 3 | c, or a + b ≡ c (mod 3), or a ≡ b ≡ 0 (mod 3), then A(3M) ≡ A(M) (mod 3^{3r}). Equivalently A(n·3^r) ≡ A(n·3^{r−1}) (mod 3^{3r}) for all n, r ≥ 1.

**Observation (not part of the theorem).** In the remaining residue classes (3 ∤ c, a + b ≢ c, and not both a, b ≡ 0 mod 3) the exponent 3r − 1 of (i) is attained in the data: e.g. (a,b,c) = (−1,−3,1) (A352373), (1,−1,1) (A002003) and (1,−1,2) (A103885) have v_3(A(3) − A(1)) = 2, and the sweep `numerics/out/theoremF_p3_sweep.txt` (−4 ≤ a, b ≤ 5, c ≤ 3, r ≤ 3) shows slack −1 for some (r, m) in every such class; the proof gives the exact leading digit (Remark 1). In the class a ≡ b ≡ 0 the data show slack ≥ 1 (consistent with the proof, which gives one extra power there).

**Corollary (Bala's conjectures at p = 3).** The instances of `proofs/TheoremF-p-ge-5.md` §5 are A119259 = A_{(2,−1,1)} (a+b = 1 = c), A333561 = A_{(3,−1,2)} (a+b = 2 = c), A333562 = A_{(4,−1,3)} (3 | c), A333565(n) = 2·A119259(n) − (−1)^n and A333564(n) = (A119259(n) − (−1)^n)/2. Since (−1)^{3M} = (−1)^M and 2 is a 3-adic unit, each of these five sequences satisfies a(n·3^r) ≡ a(n·3^{r−1}) (mod 3^{3r}) for all n, r ≥ 1. Together with Theorem F (p ≥ 5) this proves the cubic tower for all primes p ≥ 3 for all five, in particular Bala's "p ≥ 3" conjecture on A333565. For A352373 = A_{(−1,−3,1)} the class is excluded, matching the observed valuation 3r − 1 (its conjecture is stated for p ≥ 5 and was proved in the p ≥ 5 note).

## 1. Set-up (p = 3)

Imports. This note takes three things from `proofs/TheoremF-p-ge-5.md` and proves everything else here: Lemma 1 there (the reduced logarithm, valid for every odd p), Lemma G below (three coefficient identities whose proofs use only 3 | T), and the §5 identities expressing the OEIS instances as A_{(a,b,c)} (used only in the Corollary).


U := Σ_{j≥1, 3∤j} x^j/j, V := Σ_{j≥1, 3∤j} (−1)^{j+1} x^j/j, L := aV − bU = Σ_{3∤i} ℓ_i x^i/i with ℓ_i := a(−1)^{i+1} − b ∈ ℤ. All three lie in ℤ_(3)[[x]] and contain no monomial x^{3t}.

Lemma 1 of the p ≥ 5 note holds verbatim for p = 3: φ(x)³ = φ(x³)·exp(3L(x)) in ℚ[[x]]. Hence, with N = 3M,

    φ(x)^N = φ(x³)^M · exp(N L(x)).                                                           (1)

ψ := x φ'(x)/φ(x) = a x/(1+x) − b x/(1−x) = Σ_{i≥1} ℓ_i x^i ∈ ℤ[[x]] (the same ℓ_i). D := y d/dy on ℚ[[y]] (and on Laurent series).

**Cartier operator.** For f = Σ f_i x^i put C(f) := Σ_t f_{3t} y^t. It is ℚ-linear and
 (C1) C(h(x³)·f(x)) = h(y)·C(f) for all h, f;
 (C2) if f ∈ ℤ_(3)[[x]] then f(x)³ ≡ f(x³) (mod 3ℤ_(3)[[x]]) (multinomial theorem), hence C(f³) ≡ f(y) (mod 3ℤ_(3)[[y]]).

**The functional.** For f ∈ ℚ[[y]] let λ_M(f) := [y^{cM}] φ(y)^M f(y) = Σ_{s=0}^{cM} γ_s f_{cM−s}, where φ(y)^M = Σ γ_s y^s, γ_s ∈ ℤ. λ_M is ℚ-linear, maps ℤ_(3)[[y]] to ℤ_(3), λ_M(1) = A(M), and for f ∈ ℤ_(3)[[y]] the residue λ_M(f) mod 3 depends only on f mod 3 (f − f′ ∈ 3ℤ_(3)[[y]] ⇒ λ_M(f − f′) ∈ 3ℤ_(3)).

## 2. Four lemmas

**Lemma A (exact forms).** For every g ∈ ℚ[[y]] and M ≥ 1: λ_M(Dg) = −M·λ_M((ψ − c) g). In particular λ_M(ψ − c) = 0.
Proof. In the Laurent series ring, D(φ^M y^{−cM} g) = φ^M y^{−cM}·(M ψ g − cM g + Dg), because D(φ^M) = M φ^{M−1} Dφ = M φ^M ψ and D(y^{−cM}) = −cM y^{−cM}. The constant term of D(anything) is 0 (D multiplies the coefficient of y^k by k), and [y^0](φ^M y^{−cM} h) = λ_M(h). Take g = 1 for the last claim (M ≠ 0). ∎

**Lemma B (expansion).** As an identity in ℚ,  A(N) − A(M) = Σ_{j≥2} (N^j/j!)·λ_M(C(L^j)), with every λ_M(C(L^j)) ∈ ℤ_(3) and all sums finite.
Proof. By (1) and (C1), A(N) = [x^{3cM}] φ(x³)^M exp(NL) = [y^{cM}] φ(y)^M · C(exp(NL)) = Σ_{j≥0} (N^j/j!) λ_M(C(L^j)). Here C(L⁰) = 1 gives λ_M(1) = A(M), and C(L) = 0 since L has no monomial x^{3t}. Only j ≤ 3cM contribute ([x^{3t}]L^j = 0 for j > 3t, t ≤ cM). L ∈ ℤ_(3)[[x]] gives C(L^j) ∈ ℤ_(3)[[y]]. ∎

**Lemma C (sizes).** v_3(N²/2) = 2r, v_3(N³/6) = 3r − 1, and v_3(N^j/j!) ≥ 3r for all j ≥ 4.
Proof. v_3(N) = r. v_3(j!) = (j − s_3(j))/2 ≤ (j−1)/2 (s_3 = digit sum). For j ≥ 5: jr − (j−1)/2 − 3r = (j−3)r − (j−1)/2 ≥ (j−3) − (j−1)/2 = (j−5)/2 ≥ 0. For j = 4: 4r − v_3(24) = 4r − 1 ≥ 3r. ∎

**Lemma D (the cubic term).** (N³/6)·λ_M(C(L³)) ≡ (9M³/2)·λ_M(L) (mod 3^{3r}).
Proof. N³/6 = 9M³/2. By (C2), C(L³) = L(y) + 3R with R ∈ ℤ_(3)[[y]]; so the difference is (27M³/2) λ_M(R), of valuation ≥ 3 + 3(r−1) = 3r. ∎

## 3. Harmonic sums at p = 3 and the series g

For e ≥ 1 let R_e := {u : 0 < u < 3^e, 3 ∤ u}, S_k := Σ_{u∈R_e} u^{−k}, S_k^± := Σ_{u∈R_e} (−1)^{u+1} u^{−k}.

**Lemma E.** (a) S_2 ≡ −3^{e−1} (mod 3^e). (b) 2S_1 ≡ 3^{2e−1} (mod 3^{2e}). (c) S_2^± ≡ 0 (mod 3^e).
Proof. (a) u ↦ u^{−1} (mod 3^e) permutes R_e, so S_2 ≡ Σ_{u∈R_e} u² = Σ_{v=1}^{X−1} v² − 9 Σ_{w=1}^{X/3−1} w² with X = 3^e. The right side equals X(X−1)(2X−1)/6 − X(X−3)(2X−3)/18 = X(2X² − 3)/9 = 2·3^{3e−2} − 3^{e−1} ≡ −3^{e−1} (mod 3^e). (Check e = 1: S_2 = 5/4 ≡ 2 ≡ −1.)
(b) 3^e is odd, so u ↦ 3^e − u pairs off R_e without fixed points. 1/(3^e − u) = −u^{−1}(1 − 3^e/u)^{−1} ≡ −u^{−1} − 3^e u^{−2} (mod 3^{2e}), hence 1/u + 1/(3^e−u) ≡ −3^e u^{−2} (mod 3^{2e}); summing over all u ∈ R_e (each pair twice) gives 2S_1 ≡ −3^e S_2 ≡ 3^{2e−1} (mod 3^{2e}) by (a).
(c) The even u ∈ R_e are u = 2v with v ∈ R_e, v < 3^e/2, so Σ_{u even} u^{−2} = ¼ Σ_{v∈R_e, v<3^e/2} v^{−2} ≡ ¼·½ S_2 (mod 3^e) (the map v ↦ 3^e − v swaps the two halves of R_e and (3^e−v)^{−2} ≡ v^{−2} mod 3^e). So Σ_{even} ≡ S_2/8, Σ_{odd} ≡ 7S_2/8 and S_2^± = Σ_{odd} − Σ_{even} ≡ 3S_2/4 ≡ 0 (mod 3^e) by (a). ∎

**Lemma F.** Let T = ℓ·3^e with e ≥ 1 and 3 ∤ ℓ, H_T := Σ_{0<i<T, 3∤i} 1/i and H_T^± := Σ_{0<i<T, 3∤i} (−1)^{i+1}/i. Then
 (a) H_T ≡ −3^{2e−1} (mod 3^{2e}); in particular v_3(H_T) = 2e − 1;
 (b) if T is even, H_T^± ≡ 0 (mod 3^{2e}).
Proof. Write i = β3^e + u, 0 ≤ β < ℓ, u ∈ R_e; (β3^e+u)^{−1} = u^{−1}(1 + β3^e/u)^{−1} ≡ u^{−1} − β3^e u^{−2} (mod 3^{2e}).
(a) H_T ≡ ℓ S_1 − 3^e S_2 · ℓ(ℓ−1)/2 (mod 3^{2e}). By Lemma E, 3^e S_2 ≡ −3^{2e−1} and S_1 ≡ 3^{2e−1}·½ (mod 3^{2e}) (2 is a unit). So H_T ≡ 3^{2e−1}·[ℓ/2 + ℓ(ℓ−1)/2] = 3^{2e−1}·ℓ²/2 ≡ 3^{2e−1}·(1/2) ≡ −3^{2e−1} (mod 3^{2e}), using ℓ² ≡ 1 and 1/2 ≡ −1 (mod 3).
(b) (−1)^{β3^e+u+1} = (−1)^β (−1)^{u+1} as 3^e is odd, so H_T^± ≡ Σ_{β<ℓ} (−1)^β (S_1^± − β 3^e S_2^±) (mod 3^{2e}). T even forces ℓ even, hence Σ_{β<ℓ}(−1)^β = 0 and Σ_{β<ℓ}(−1)^β β = −ℓ/2 ∈ ℤ; thus H_T^± ≡ (ℓ/2) 3^e S_2^± ≡ 0 (mod 3^{2e}) by Lemma E(c). ∎

**Lemma G (Lemma 4 of the p ≥ 5 note; the proof there uses only 3 | T).** For T ≡ 0 (mod 3): [x^T]U² = 2H_T/T, [x^T]V² = (−1)^T·2H_T/T, [x^T]UV = (1 + (−1)^T)·H_T^±/T.

**Lemma H (the series g).** Put g_t := [x^{3t}] L² / t (t ≥ 1) and g := Σ_{t≥1} g_t y^t. Then
 (a) g ∈ ℤ_(3)[[y]] and D g = C(L²);
 (b) g_t ≡ a²(−1)^t + b² (mod 3) for every t ≥ 1; i.e. ḡ := g mod 3 equals −a²y/(1+y) + b²y/(1−y) = y[(b² − a²) + (a² + b²) y]/(1 − y²) in F_3[[y]].
Proof. D g = Σ t g_t y^t = Σ_t [x^{3t}]L² y^t = C(L²) (note [x^0]L² = 0), so (a) follows once g_t ∈ ℤ_(3) is shown. Integrality: by Lemma G, g_t = (1/t)[a²·(−1)^T·2H_T/T − 2ab·(1+(−1)^T)H_T^±/T + b²·2H_T/T] with T = 3t = ℓ3^e, so every term has denominator T·t = ℓ²3^{2e−1}; by Lemma F(a) v_3(H_T) = 2e−1 and by Lemma F(b) v_3(H_T^±) ≥ 2e when T is even (the H_T^± term is absent when T is odd), hence g_t ∈ ℤ_(3). (The same expressions give (b).) For (b) write T = 3t = ℓ3^e with 3 ∤ ℓ, so e = 1 + v_3(t) and t = ℓ3^{e−1}. By Lemma F(a), H_T = −3^{2e−1} + 3^{2e}κ with κ ∈ ℤ_(3); by Lemma G, [x^T]U²/t = 2H_T/(T t) = 2(−3^{2e−1} + 3^{2e}κ)/(ℓ² 3^{2e−1}) = (2/ℓ²)(−1 + 3κ) ≡ −2 ≡ 1 (mod 3) (ℓ² ≡ 1). Likewise [x^T]V²/t ≡ (−1)^T = (−1)^t (T = 3t). If t is odd, [x^T]UV = 0; if t is even, T is even and Lemma F(b) gives H_T^± = 3^{2e}κ', so [x^T]UV/t = 2·3^{2e}κ'/(ℓ² 3^{2e−1}) ≡ 0 (mod 3). Since L² = a²V² − 2ab UV + b²U², g_t ≡ a²(−1)^t + b² (mod 3). The closed form: Σ_{t≥1}(−1)^t y^t = −y/(1+y), Σ_{t≥1} y^t = y/(1−y). ∎

## 4. The reduction and the proof

**Proposition I (reduction; all a, b, c).**  A(3M) − A(M) ≡ (9M³/2) · λ_M( L − (ψ − c)·g )  (mod 3^{3r}).  Consequently Theorem F₃(i) holds.
Proof. By Lemmas B and C, A(N) − A(M) ≡ (N²/2) λ_M(C(L²)) + (N³/6) λ_M(C(L³)) (mod 3^{3r}). By Lemma H(a) and Lemma A, λ_M(C(L²)) = λ_M(Dg) = −M λ_M((ψ−c)g). By Lemma D the cubic term is ≡ (9M³/2) λ_M(L). Since N²/2 = 9M²/2, the sum is (9M³/2)·[λ_M(L) − λ_M((ψ−c)g)]. Finally v_3(9M³/2) = 3r − 1 and λ_M(L − (ψ−c)g) ∈ ℤ_(3) (L, g ∈ ℤ_(3)[[y]], ψ ∈ ℤ[[y]]). ∎

Notation for the last step: bars denote reduction mod 3 (series in F_3[[y]]); α := a − b, β := −(a + b), so ℓ_i ≡ α for odd i and ℓ_i ≡ β for even i, i.e.

    ψ̄ = α y/(1−y²) + β y²/(1−y²) = y(α + βy)/(1 − y²).

**Lemma J (an identity in F_3[[y]]).**
 (a) L̄ = Dψ̄ = y(α + 2βy + αy²)/(1 − y²)².
 (b) If 3 ∤ c and a + b ≡ c (mod 3): L̄ = (ψ̄ − c)·ḡ.
 (c) If 3 | c: L̄ = ψ̄·(ḡ + K₀) with the constant K₀ := 1 if a ≢ b (mod 3), K₀ := 2 if a ≡ b (mod 3).
Proof. (a) For 3 ∤ i, 1/i ≡ i (mod 3) (i ≡ ±1), so L̄ = Σ_{3∤i} iℓ_i y^i = Σ_{i≥1} iℓ_i y^i = Dψ̄ (the omitted terms have coefficient iℓ_i ≡ 0). The rational form is a direct differentiation: d/dy [y(α+βy)/(1−y²)] = [(α+2βy)(1−y²) + 2y²(α+βy)]/(1−y²)² = (α + 2βy + αy²)/(1−y²)².
(b) β ≡ −c, so ψ̄ − c = [y(α+βy) − c(1−y²)]/(1−y²) = (αy − c)/(1−y²). With Lemma H(b), (ψ̄−c)ḡ = y(αy − c)[(b²−a²) + (a²+b²)y]/(1−y²)², and we must show
    (αy − c)·[(b² − a²) + (a² + b²) y] = α + cy + αy²   in F_3[y]
(note 2β ≡ −2c ≡ c). Constant term: −c(b²−a²) = cα(a+b) ≡ c²α = α (c² ≡ 1). Coefficient of y²: α(a²+b²). Coefficient of y: α(b²−a²) − c(a²+b²) = −α²(a+b) − c(a²+b²) ≡ −c(α² + a² + b²). Now a + b ≡ c ≢ 0 leaves two cases: a ≢ b, which forces {a, b} ≡ {0, c}, so α² ≡ 1 and a² + b² ≡ 1: the y² coefficient is α and the y coefficient is −2c ≡ c; or a ≡ b ≡ 2c, so α = 0 and a² + b² ≡ 2: the y² coefficient is 0 = α and the y coefficient is −2c ≡ c. ∎(b)
(c) Here ψ̄·(ḡ + K₀) = y(α+βy)·[K₀ + (b²−a²)y + (a²+b²−K₀)y²]/(1−y²)², so we must show
    (α + βy)·[K₀ + (b²−a²) y + (a²+b²−K₀) y²] = α + 2βy + αy²   in F_3[y].
Use b² − a² = αβ. Case a ≢ b (α² ≡ 1), K₀ = 1: constant α; y: α·αβ + β = 2β; y²: α(a²+b²−1) + β·αβ = α(a² + b² + β² − 1) and a² + b² + (a+b)² = 2(a² + ab + b²) = 2((a−b)² + 3ab) ≡ 2α² = 2, so the y² coefficient is α; y³: β(a²+b²−1), which vanishes because for (a,b) ≡ (0,±1), (±1,0) we have a²+b² ≡ 1, while for (a,b) ≡ (1,2), (2,1) we have β = −(a+b) ≡ 0. Case a ≡ b ≢ 0 (α = 0, a² = b² = 1, a²+b² = 2), K₀ = 2: the left side is βy·[2 + 0·y + 0·y²] = 2βy, the right side is 2βy. Case a ≡ b ≡ 0: both sides vanish. ∎

**Proof of Theorem F₃(ii).** By Proposition I it suffices to show λ_M(L − (ψ−c)g) ≡ 0 (mod 3), and λ_M(f) mod 3 depends only on f̄ (all series involved lie in ℤ_(3)[[y]]). In case 3 ∤ c, a+b ≡ c, Lemma J(b) gives L̄ − (ψ̄ − c)ḡ = 0. In case 3 | c, c̄ = 0 and Lemma J(c) gives L̄ − (ψ̄ − c̄)ḡ = ψ̄ K₀ = (ψ̄ − c̄) K₀. In case a ≡ b ≡ 0 (mod 3), every ℓ_i is ≡ 0, so L̄ = 0, ψ̄ = 0 and (by Lemma H(b)) ḡ = 0, whence L̄ − (ψ̄ − c̄)ḡ = 0 for every c. In all cases λ_M(L − (ψ−c)g) ≡ K₀·λ_M(ψ − c) = 0 (mod 3) by Lemma A (with K₀ := 0 in the first and third cases). ∎

## 5. Remarks

1. (Exact leading digit.) Proposition I gives, for every (a,b,c), (A(3M) − A(M))/3^{3r−1} ≡ (m³/2)·λ_M(L̄ − (ψ̄−c)ḡ) ≡ −m³·λ_M(L̄ − (ψ̄ − c)ḡ) (mod 3), where M = 3^{r−1}m. In the classes excluded from (ii) the series L̄ − (ψ̄−c)ḡ is not of the form (ψ̄−c)·const (checked for all 27 residue triples, `theoremF_p3_proof_checks.txt` part V3 and test T9 of `referee_theoremF_p3.py`; the only triples with a constant K₀ are those of (ii), where for a ≡ b ≡ 0 both sides vanish with K₀ = 0, and every constant works only if moreover 3 | c), and the data show the digit is nonzero for suitable m (part V1 and the sweep); e.g. for A352373 the digit is nonzero exactly at m ≡ 1 (mod 3) and zero at m ≡ 2 (mod 3) in all tested (r, m) (`numerics/out/rereview_theoremF_p3_lemmas.txt`).
2. (Why p = 3 is different.) For p ≥ 5 the quadratic term alone has valuation ≥ 3r termwise (Lemma 3/Lemma 6 of the p ≥ 5 note) and the cubic term too (p ∤ 3!). At p = 3 both are one power short, and Proposition I shows they combine into (9M³/2)·λ_M(L − (ψ−c)g): the exact-form identity trades the quadratic term for a multiple of M, after which the obstruction is a mod-3 statement. The same reduction can be run for any odd p; at p ≥ 5 it is not needed.
3. (Sharpness of (i) and of the hypothesis.) By Remark 1 the hypothesis in (ii) is exactly the vanishing of the mod-3 digit for all m. The sweep over −4 ≤ a, b ≤ 5, c ≤ 3 found, for 3 ∤ c, no (a,b) outside the classes of (ii) (a + b ≡ c or a ≡ b ≡ 0) that holds for all tested (r,m); the apparent exceptions are coincidences for small m (the four sweep survivors (−3,−2,2), (−2,−3,2), (3,4,2), (4,3,2) all first fail at m = 5) or degenerate triples with A ≡ 0 (deg φ^N < cN, e.g. (0,1,2)); for c = 3 every (a,b) holds, as (ii) predicts.
4. (Numerical confirmation.) `theoremF_p3_proof_checks.py`: (V1) Proposition I holds exactly for 288 triples (a,b,c,r,m) (16 pairs (a,b) × c ∈ {1,2,3} × r ≤ 3 × m ≤ 2), and v_3(A(N)−A(M)) ≥ 3r−1 in all of them; (V2) g_t ∈ ℤ_(3) and g_t ≡ a²(−1)^t + b² for t ≤ 200; (V3) the identity L̄ = (ψ̄−c)(ḡ + K₀) holds in exactly the residue classes of (ii) and in no other (the script's three "MISMATCH" lines are the class a ≡ b ≡ 0, where both sides vanish for K₀ = 0 and the script's predicted K₀ was arbitrary); (V4) λ_M(ψ−c) = 0 exactly. Independent check script: `numerics/scripts/referee_theoremF_p3.py` (T0–T12, 0 failures; the theorem tested for 18 + 11 + 9 good triples and 10 bad ones, r ≤ 3, m ≤ 7: slack exactly 0 in the two main classes, ≥ 1 in the class a ≡ b ≡ 0, −1 in the bad ones). The theorem itself: `theoremF_p3_conjecture_check.py` (r ≤ 4, m ≤ 8) and `theoremF_p3_sweep.py`. Independent re-check (2026-10-15): `numerics/scripts/rereview_theoremF_p3_lemmas.py` (Lemmas A–J, Proposition I in 480 cases up to r = 4, Theorem F₃ for 36 triples, r ≤ 4, m ≤ 8; the only two failing lines were two sentences of Remark 1, corrected above).

## 6. References
- P. Bala, OEIS A119259, A333561, A333562, A333564, A333565, A352373 (conjectures).
- `proofs/TheoremF-p-ge-5.md` (p ≥ 5; Lemmas 1 and 4 reused here).
- Exact-form (total-derivative) arguments for coefficient functionals are classical in the theory of Gauss/Dwork congruences (e.g. F. Beukers, M. Vlasenko, Dwork crystals I–III, 2019–2021, where the Cartier operator on forms f·dx/x is the basic tool); the specific use here (Lemma A combined with the reduction of Proposition I) was worked out for this note.
