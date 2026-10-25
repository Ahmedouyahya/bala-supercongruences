# Theorem F (p ≥ 5) in Lean — route b: the paper's proof on Epoch's power-series exponential (decided 2026-10-16)

Why this route: one general theorem covers A333561, A333562, A352373 and the p ≥ 5 part of A333565 (and A119259, A103885), the
Lean proof follows `proofs/TheoremF-p-ge-5.md` step by step, and the same set-up is reused for the p = 3 case (Theorem F₃).
Base: `fc-ws/BalaCheck/EpochExp.lean` = Epoch AI's accepted A333042 proof (namespace `Epoch333042`, inside it `Super`), body
byte-identical. Relevant there: `expS`, `IsExpOf`, `isExpOf_iff_deriv`, `expS_add`, `expS_nsmul`, `expS_mul_expS_neg`,
`expand_expS`, `coeff_expS` (coeff n (expS F) = Σ_{ℓ≤n} (ℓ!)⁻¹ coeff n (F^ℓ)), `exp_tail`, `coeff_mul_expand`
(coeff (n t) (E · expand t A) = Σ_{w≤n} coeff (n t − t w) E · coeff w A), `frob_trunc`, `dwork`, the valuation predicate
`V p k q` (padicNorm p q ≤ p^(−k)) with `V_add/V_sub/V_mul/V_sum/V_pow/V_int_iff_dvd/V_inv_unit/...`, `factorial_val_bound`,
`padicValNat_factorial_le`. Wolstenholme (Σ_{k < b p^r, p∤k} 1/k = 0 in ZMod (p^(2r)), p ≥ 5): lemma `wolstenholme` in Epoch's
accepted A364173 proof (`LeanOpenProblems-results/runs/oeis-lite-200usd-lit-ant-a1zwt7jqfgg8aao6/oeis_364173_conjecture_0/
Submission/Spec.lean`, line 187) — stage it the same way (namespace-wrapped, body byte-identical) or prove it.

## Definitions (p prime, a b : ℤ, c : ℕ)
- ℓ₊ := mk (fun j ↦ if j = 0 then 0 else (−1)^(j+1)/j) (= log(1+x)), ℓ₋ := mk (fun j ↦ if j = 0 then 0 else −1/j) (= log(1−x)).
- F := a•ℓ₊ + b•ℓ₋;  Φ N := expS ((N:ℚ) • F)  (= φ(x)^N, φ = (1+x)^a (1−x)^b);  A N := coeff (c*N) (Φ N).
- U := mk (j ↦ if p ∣ j then 0 else 1/j), V := mk (j ↦ if p ∣ j then 0 else (−1)^(j+1)/j), L := a•V − b•U.
## Steps
1. expS ℓ₊ = 1 + X and expS ℓ₋ = 1 − X (IsExpOf via `isExpOf_iff_deriv`); hence Φ N has integer coefficients and, for the
   instances, is a product of (1+X)^k, (1−X)^k and their inverses (Mathlib `PowerSeries.invOneSubPow`, coefficients C(n+k−1,k)).
2. Frobenius–exp identity (Lemma 1), as a COEFFICIENT identity: (p:ℚ)•F = expand p F + (p:ℚ)•L for odd p
   ([x^j]: p ∤ j: both sides p·ℓ_j; j = p i: p·(−1)^(pi+1)/(pi) = (−1)^(i+1)/i, L_j = 0). Hence, with `expS_add`, `expand_expS`:
   Φ (p M) = expand p (Φ M) * expS ((pM:ℚ) • L).
3. Expansion (paper (1)): A(pM) − A(M) = Σ_{w < cM} coeff (p(cM − w)) (expS (N•L)) · coeff w (Φ M), N = pM (`coeff_mul_expand`,
   the w = cM term is A(M) since coeff 0 (expS _) = 1).
4. Harmonic sums: H_T := Σ_{0<i<T, p∤i} 1/i. For T = ℓ p^e (e ≥ 1): H_T ≡ 0 mod p^(2e) (Wolstenholme with b = ℓ, r = e).
   Alternating: H_T^± := Σ (−1)^(i+1)/i = H_T − H_{T/2} for T even (even i = 2i′ contributes 1/(2i′)), so H_T^± ≡ 0 mod p^(2e) too
   (T/2 = (ℓ/2)p^e). No separate S_2^± analysis is needed.
5. Lemma 4: for p | T: [x^T]U² = 2H_T/T, [x^T]V² = (−1)^T·2H_T/T, [x^T](UV) = (1 + (−1)^T)H_T^±/T (finite sums over i + j = T;
   p | T makes p ∤ i ⇔ p ∤ T − i; 1/(ij) = (1/T)(1/i + 1/j)). Hence V p (v_p T) ([x^T] L²).
6. ε-bound: for T = p T′ (T′ ≥ 1), ε_T := coeff T (expS (N•L)) = Σ_ℓ (N^ℓ/ℓ!) coeff T (L^ℓ) (`coeff_expS`): ℓ = 1 term 0 (p | T);
   ℓ = 2: V p (2r + v_p T); ℓ ≥ 3: L^ℓ p-integral, V p (3r) (N^ℓ/ℓ!) for p ≥ 5 (v_p(ℓ!) ≤ (ℓ−1)/4 ≤ (ℓ−3)r for ℓ ≥ 4; p ∤ 6).
   So V p (min(2r + v_p T, 3r)) ε_T, r := v_p N = 1 + v_p M.
7. Frobenius lifting (Lemmas 5–6): for f with integer coefficients, f^p ≡ expand p f (mod p) (`frob_trunc`); X ≡ Y mod p^k ⇒
   X^p ≡ Y^p mod p^(k+1); so for M = p^(r−1) m (p ∤ m) and s ≥ 1 with σ := v_p(s) ≤ r − 2: V p (r − 1 − σ) (coeff s (Φ M)).
8. Assembly (paper §4): each term of step 3 has valuation ≥ 3r (τ := v_p(cM − w): τ ≥ r − 1 → step 6 alone; τ ≤ r − 2 → σ = τ,
   steps 6 + 7). Result: Theorem F: ∀ p prime ≥ 5, ∀ M ≥ 1, V p (3(1 + v_p M)) (A(pM) − A(M)); equivalently for n p^r vs n p^(r−1).
9. Instances (target formulas as coefficients): A333561: Σ_{k≤2n} C(3n,2n−k)C(n+k−1,k) = coeff (2n) ((1+X)^{3n}(1−X)^{−n}),
   (a,b,c) = (3,−1,2). A333562: target = Σ_{k≤3n} C(4n,3n−k)C(n+k−1,k) by `BalaCheck/A333562Ident.lean` (`A333562.a_eq_rep`),
   = coeff (3n) ((1+X)^{4n}(1−X)^{−n}), (4,−1,3). A352373: target = Σ_{k≤n/2} C(3n−2k−1,n−2k)C(n+k−1,k)
   = coeff n ((1−X)^{−2n}(1−X²)^{−n}) = coeff n ((1+X)^{−n}(1−X)^{−3n}), (−1,−3,1). A333565 (p ≥ 5 part): later.
Numerics: `numerics/scripts/theoremF_framing_tests.py`, `rereview_theoremF_p5_identities.py`, `rereview_theoremF_p5_valuations.py`
(all steps, 0 failures).
