# Numerics

All scripts use exact arithmetic (Python integers, `fractions.Fraction`, or sympy for the symbolic checks). Run from the repository root with `python3 -I numerics/scripts/<name>.py`; the Maxima script with `maxima -b numerics/scripts/a361711_zeilberger.mac`. The archived outputs are in `numerics/out/`, one file per script with the same base name. Scripts marked "exploration" are search-phase experiments that no proof depends on; they are kept because the notes or the log cite their negative or structural results.

## Where the scripts write

The scripts were written when they lived directly in `numerics/` with `out/` as a sibling; apart from the path fixes in group 3 they have not been modified. Three groups:

1. Most scripts print to standard output; their archived output is the redirected terminal output (`python3 -I numerics/scripts/<name>.py > numerics/out/<name>.txt`).
2. These write to a directory `out/` next to the script, i.e. `numerics/scripts/out/` in this layout, which must exist (or be a link to `../out`) before they run: `a376462_deep_direct_test.py`, `a376462_deep_direct_test2.py`, `lemmaB_k15_residue_check.py`, `referee_A_shifted_lemmas.py`, `referee_B_shifted_assembly.py`, `referee_B_deeper_cases.py`, `referee_B_wider_primes.py`, `rereview_a370092_amice.py`, `rereview_a370092_identities.py`, `rereview_a370092_lemmaB.py`, `rereview_a370092_periods.py`, `rereview_a370092_pow2_deep.py`, `rereview_a370092_profile_k4.py`, `rereview_shifted_exact.py`, `rereview_shifted_harmonic.py`, `rereview_shifted_towers.py`, `rereview_shifted_classKJ.py`, `rereview_shifted_classSB.py`, `rereview_shifted_literature.py`, `rereview_shifted_misc.py`, `theoremF_deep_direct_sweep.py`, `theoremF_deep_direct_sweep2.py`. Likewise `a361711_zeilberger_check.py` reads `out/a361711_zeilberger_certificate.txt` next to itself, and `a361711_zeilberger.mac` writes `zeil_out.txt` into the current directory (the archived copy is `out/a361711_zeilberger_certificate.txt`).
3. These locate the repository root from their own path (they originally contained an absolute path to the original working folder; that was replaced on 2026-10-16 and is the only change to them) and write their output directly into `numerics/out/`, overwriting the archived copy: `rereview_theoremF_oeis_extra.py`, `rereview_theoremF_p3_lemmas.py`, `rereview_theoremF_p5_identities.py` (also reads `statements/STATEMENTS.md`), `rereview_theoremF_p5_valuations.py`, `rereview_short_A361711.py` (prints to standard output; reads `numerics/out/a361711_zeilberger_certificate.txt`). `fractional_factorial_sweep.py` originally read OEIS records from a temporary directory of the original machine; since 2026-10-16 it reads the first terms of A364172–A364184 from `numerics/data/oeis_A364172-A364184.json` (fetched from the OEIS on 2026-10-16, with revision numbers), and its re-run output is identical to the archived `out/fractional_factorial_sweep.txt`. `a376462_transforms.py` fetches OEIS data over the network.

The `rereview_shifted_*.py` and `referee_B_*.py` scripts import `rereview_shifted_common.py` from their own directory.

## Scripts

| Script | What it tests | Output |
|---|---|---|
| `a361711_factors.py` | exploration: factor-by-factor p-adic behaviour of a(M) at M = p^k (A361711) | `a361711_factors.txt` |
| `a361711_harmonic_reduction.py` | A361711 Lemma 2: the exact identities (E1), (E2), p ≤ 47, p^k ≤ 60000; the prime-power Lehmer congruence of §4 | `a361711_harmonic_reduction.txt` |
| `a361711_two_lemmas.py` | A361711 §0 and §4: v_p(a(p^k) − a(p^{k−1})) for p ≤ 43 and the two Morley-type congruences X ≡ 4^φ, Y ≡ 4^{−φ} (mod p^{3k}) | `a361711_two_lemmas.txt` |
| `a361711_valuations.py` | L1: v_p(a(p^k) − a(p^{k−1})) ≥ 3k for A361711 | standard output (not archived) |
| `a361711_zeilberger.mac` | Maxima: Zeilberger certificate for F(n,k) = (−1)^k C(n,k)² C(n−2,k) (A361711 Lemma 1) | `a361711_zeilberger_certificate.txt` |
| `a361711_zeilberger_check.py` | A361711 Lemma 1: the certificate as a rational-function identity (sympy), the order-2 recurrence, the closed forms satisfy it | `a361711_zeilberger_check.txt` |
| `a363983_oss_steps.py` | A363983 §4: Lemma 5, identities (1)–(3), the chain of Lemma 6, Lemmas 2–4 | `a363983_oss_steps.txt` |
| `a363983_structure.py` | exploration: scaled vs unscaled terms of A363983 at N = np^r | `a363983_structure.txt` |
| `a364172_a364179_integrality.py` | A364172/A364179 addendum: integrality for n ≤ 200 and the valuation formulas v_3(A364172(n)), v_2(A364179(n)) | `a364172_a364179_integrality.txt` |
| `a364172_q2_digits.py` | A364172 at q = 2: v_2(a(n)) ≥ 0 and its exact pattern | `a364172_q2_digits.txt` |
| `a370092_periodicity.py` | L1: A370092 mod k eventually periodic with period dividing φ(k), 3 ≤ k ≤ 40 | `a370092_periodicity.txt` |
| `a370092_powers_of_two.py` | A370092 §5: minimal periods mod 2^e and p^e versus φ and λ, v_2(c_k), v_2(g_k), identity (1) | `a370092_powers_of_two.txt` |
| `a370092_termwise_2adic.py` | A370092 Prop. 2: termwise v_2(b_k) + v_2(g_k) ≥ e | `a370092_termwise_2adic.txt` |
| `a376462_beukers_architecture.py` | A376462 shifted, §9: class decomposition S, K, J, B and first-order models at r = 2, 3 | `a376462_beukers_architecture.txt` |
| `a376462_classJ_dissection.py` | A376462 shifted, §5: class-J pieces with the coefficient ρ′ | `a376462_classJ_dissection.txt` |
| `a376462_classS_strata.py` | A376462 shifted, §7: class-S strata by σ | `a376462_classS_strata.txt` |
| `a376462_deep_direct_test.py` | L1: both A376462 congruences from the OEIS definition, deep cases (r = 2 to p = 31, r = 3, 4) | `a376462_deep_direct_test.txt` |
| `a376462_deep_direct_test2.py` | L1: as above, r up to 5 (N = 3125) | `a376462_deep_direct_test2.txt` |
| `a376462_dual_identity.py` | negative result (shifted §8.4): no (26)-type dual identity for A376462 | `a376462_dual_identity.txt` |
| `a376462_dual_sequence.py` | exploration: dual sequence b(n) and the negative-index relation a(N−1) = F(−N, …) | `a376462_dual_sequence.txt` |
| `a376462_final_lemma_checks.py` | A376462 shifted, §9: failure of Beukers' (10), ingredients of Lemma 2.5, §7 decoupling, Lemma 2.1 | `a376462_final_lemma_checks.txt` |
| `a376462_laurent.py` | A376462 first note §0: a(n) = CT[Λ^n] and the Newton polytope | `a376462_laurent.txt` |
| `a376462_lemma5_dissection.py` | A376462 shifted, §9: the induction of §4 piece by piece (A_s, X_{s,i}, Y_s, X̂) | `a376462_lemma5_dissection.txt` |
| `a376462_lemma_bank_checks.py` | A376462 shifted, Lemma 3.4(a)–(c), Lemma 2.7, Lemma 2.5 on general blocks | `a376462_lemma_bank_checks.txt` |
| `a376462_moment_subconjecture.py` | exploration: moment sub-conjecture from the r = 2 dissection | `a376462_moment_subconjecture.txt` |
| `a376462_multiparam_shift_test.py` | exploration: shifted statements for the 6-parameter family | `a376462_multiparam_shift_test.txt` |
| `a376462_multivariate.py` | A376462 first note, literature remark: multivariate extension A(pn; pd) ≡ A(n; d) (mod p³), random tests | `a376462_multivariate.txt` |
| `a376462_oss_probe.py` | exploration: intermediate congruences an OSS-type proof would need | `a376462_oss_probe.txt` |
| `a376462_oss_steps.py` | A376462 first congruence, §4: every step (classes S, K, I, B, reductions, chains, self-similarity) | `a376462_oss_steps.txt` |
| `a376462_recurrence.py` | by-product: order-3 P-recurrence for A376462 | `a376462_recurrence.txt` |
| `a376462_representations.py` | A376462 first note §0: the exact representations of a(n) | `a376462_representations.txt` |
| `a376462_second_congruence_probe.py` | exploration: structure probe of the shifted congruence | `a376462_second_congruence_probe.txt` |
| `a376462_second_r1_steps.py` | A376462 first note §5: every sub-claim of the r = 1 shifted proof | `a376462_second_r1_steps.txt` |
| `a376462_second_r2_dissect.py` | exploration: r = 2 dissection of the shifted congruence | `a376462_second_r2_dissect.txt` |
| `a376462_second_structure.py` | A376462 first note §5 and shifted §9: the re-indexed representation a(N−1) = Σ S̃(N;k,j) and the four classes | `a376462_second_structure.txt` |
| `a376462_shift_pattern.py` | A376462 shifted §9: which shifts c give a tower; theorem for p ∈ {5,7,11}, m ≤ 3, r ≤ 2 | `a376462_shift_pattern.txt` |
| `a376462_straub_shape_search.py` | negative result (first note remark, shifted §8.4): no Straub block shape among the 120 assignments | `a376462_straub_shape_search.txt` |
| `a376462_structure.py` | exploration: OSS-type structure of A376462 | `a376462_structure.txt` |
| `a376462_transforms.py` | exploration: Legendre and binomial transforms of A376462 (network access) | `a376462_transforms.txt` |
| `a376462_uniform_family_test.py` | exploration: Straub-type uniform statement for the 6-parameter family | `a376462_uniform_family_test.txt` |
| `fractional_factorial_sweep.py` | A364172–A364184 note: integer forms, integrality n ≤ 120, floor criterion, ratio tower (Theorem U) | `fractional_factorial_sweep.txt` |
| `jk_ratio_form_and_closed_forms.py` | A386548 §2, §4: Jacobsthal–Kazandzidis quotient form, p ∈ {5,7,11}; A361711 closed forms vs definition | `jk_ratio_form_and_closed_forms.txt` |
| `lemma4ii_strength.py` | A376462 shifted, Lemma 2.6 (Beukers' Lemma 4(ii) holds mod p^{t+2s}) | `lemma4ii_strength.txt` |
| `lemmaB_amice_parts.py` | A370092 Lemma B: the two Amice-type bounds, the exceptional set {3,6,7,15} | `lemmaB_amice_parts.txt` |
| `lemmaB_finite_checks.py` | A370092 Lemma B: sanity test of the Amice-type bound; finite checks for k ∈ {3,6,7,15} | `lemmaB_finite_checks.txt` |
| `lemmaB_k15_residue_check.py` | A370092 Lemma B: self-contained finite verification of v_2(S_1) ≥ ⌊k/3⌋ for k ∈ {3,6,7,15} | `lemmaB_k15_residue_check.txt` |
| `lemmaB_stirling_2adic.py` | A370092 Lemma B: v_2(k!(S(n+2^m,k) − S(n,k))) ≥ m + 1 + ⌊k/3⌋ | `lemmaB_stirling_2adic.txt` |
| `referee_A_shifted_lemmas.py` | independent check of §§0–3 of the shifted A376462 note (782 checks) | `referee_A_shifted_lemmas.txt` |
| `referee_B_shifted_assembly.py` | independent check of §§4–7 of the shifted A376462 note (357 checks) at (5,2,1), (5,2,2), (7,2,1), (5,3,1) | `referee_B_shifted_assembly.txt` |
| `referee_B_deeper_cases.py` | the same at (7,3,1), (5,3,2), (5,4,1) | `referee_B_deeper_cases.txt` |
| `referee_B_wider_primes.py` | the same at (11,2,1), (13,2,1), (7,2,2) | `referee_B_wider_primes.txt` |
| `referee_theoremF_p3.py` | independent check of Theorem F₃, tests T0–T12 | `referee_theoremF_p3.txt` |
| `rereview_a370092_amice.py` | A370092: the Amice/Colmez step (basis, unit ball, random functions) | `rereview_a370092_amice.txt` |
| `rereview_a370092_identities.py` | A370092 §§0–1: e.g.f., recurrence, G(u), (1), (P1)–(P3), the α ≤ 2 clause of Prop. 2 | `rereview_a370092_identities.txt` |
| `rereview_a370092_lemmaB.py` | A370092 Lemma B: bound (2), local expansions, the decomposition b_k = E_k + 2^{m+1}S_1 + 2^{m+2}S_2, exceptional k | `rereview_a370092_lemmaB.txt` |
| `rereview_a370092_periods.py` | A370092 Theorem for 3 ≤ k ≤ 400 with 1500 terms; start indices and minimal periods | `rereview_a370092_periods.txt` |
| `rereview_a370092_pow2_deep.py` | A370092 mod 2^α up to α = 12 | `rereview_a370092_pow2_deep.txt` |
| `rereview_a370092_profile_k4.py` | A370092: minima of v_2(b_k) − m over the lemma's range (parenthetical after Lemma B) | `rereview_a370092_profile_k4.txt` |
| `rereview_oss_a363983.py` | A363983: Lemma 5, (1)–(3), Lemma 6, Theorem, remarks; r = 3, p ∤ m and p \| m | `rereview_oss_a363983.txt` |
| `rereview_oss_a363983_wider.py` | A363983 Theorem at larger primes and depths (p ≤ 31) | `rereview_oss_a363983_wider.txt` |
| `rereview_oss_a376462.py` | A376462 first note §§0–5; r = 3, p \| m | `rereview_oss_a376462.txt` |
| `rereview_oss_lemmas.py` | Lemmas 1–4 of the A363983 note (used verbatim by the A376462 first note) | `rereview_oss_lemmas.txt` |
| `rereview_quad_A386548_congruences.py` | A386548: (JK) with slack, level form, unscaled and scaled term bounds, Theorem | `rereview_quad_A386548_congruences.txt` |
| `rereview_quad_A386548_identities.py` | A386548: formula (1) vs the series coefficient and the OEIS formula, first terms | `rereview_quad_A386548_identities.txt` |
| `rereview_quad_factorial_congruences.py` | A364175/A364178: Lemma 2, Lemma A, Lemma B, Theorem 3 with slack | `rereview_quad_factorial_congruences.txt` |
| `rereview_quad_factorial_identities.py` | A364175/A364178: integer forms, Γ identities, v_2 formulas, the integrality argument | `rereview_quad_factorial_identities.txt` |
| `rereview_shifted_classKJ.py` | A376462 shifted §§4–5 piece by piece | `rereview_shifted_classKJ.txt` |
| `rereview_shifted_classSB.py` | A376462 shifted §§6–7 and the Theorem | `rereview_shifted_classSB.txt` |
| `rereview_shifted_common.py` | shared helpers of the `rereview_shifted_*.py` scripts | none |
| `rereview_shifted_exact.py` | A376462 shifted: exact identities (Lemmas 1.1, 1.3, 3.3, 3.5, class decomposition, expansions in the proofs of 2.3, 2.5, 2.6) | `rereview_shifted_exact.txt` |
| `rereview_shifted_harmonic.py` | A376462 shifted Lemmas 2.1–2.7 with slack | `rereview_shifted_harmonic.txt` |
| `rereview_shifted_literature.py` | A376462 shifted §8: Beukers' (10) and Lemma 4(ii) | `rereview_shifted_literature.txt` |
| `rereview_shifted_misc.py` | A376462 shifted: the §5 symmetry remark on Ξ, carry composition of Lemma 3.2 | `rereview_shifted_misc.txt` |
| `rereview_shifted_towers.py` | A376462 shifted Lemmas 1.2, 3.4, 3.5, §5 (i)–(iii), the towers of §7 | `rereview_shifted_towers.txt` |
| `rereview_short_A352275.py` | A352275 note: two-parameter statement with v = min(v_p(N), v_p(S−N)), u_m vs OEIS data, −3N ≤ r < −N | `rereview_short_A352275.txt` |
| `rereview_short_A361711.py` | A361711 note: closed forms, recurrence, certificate re-derived symbolically, Lemmas 2–3 and the Theorem for 5 ≤ p ≤ 100 | `rereview_short_A361711.txt` |
| `rereview_theoremF_oeis_extra.py` | Theorem F §5: A119259, A103885, A002003, A333564 against OEIS b-file data | `rereview_theoremF_oeis_extra.txt` |
| `rereview_theoremF_p3_lemmas.py` | Theorem F₃: Lemmas A–J, Prop. I (r ≤ 4), Theorem F₃ (i)/(ii) with slack, Remarks 1 and 3 | `rereview_theoremF_p3_lemmas.txt` |
| `rereview_theoremF_p5_identities.py` | Theorem F: Lemmas 1, 4, 5, expansion (1), change of variables, the §5 instance identities | `rereview_theoremF_p5_identities.txt` |
| `rereview_theoremF_p5_valuations.py` | Theorem F: Lemmas 2, 3, 6, estimate (2), the Theorem with slack (r ≤ 3), term by term at p = 5 | `rereview_theoremF_p5_valuations.txt` |
| `second_order_block_sums.py` | exploration: second-order block sums (W1)–(W5) | `second_order_block_sums.txt` |
| `shifted_aux_integrality.py` | exploration: divisibility of V(M) and moment valuations for the shifted problem | `shifted_aux_integrality.txt` |
| `shifted_model_auxiliary.py` | exploration: class-K analysis of the model problem Σ C(n,k)²C(n+k,k) | `shifted_model_auxiliary.txt` |
| `shifted_moments_model.py` | exploration: moment congruences for the model problem | `shifted_moments_model.txt` |
| `sweep_2026-10-15.py` | L1: all statements at modest depth (A352275 and the β identity, A386548, A363983, A376462, A364175/A364178, …) | `sweep_2026-10-15.txt` |
| `theoremF_deep_direct_sweep.py` | L1: Theorem F (p ≥ 5) and Theorem F₃ (p = 3) over a, b ∈ [−5, 7], c ≤ 4 | `theoremF_deep_direct_sweep.txt` |
| `theoremF_deep_direct_sweep2.py` | L1: the same, deeper in r (p = 3 to r = 7, p = 5 to r = 4, p = 7, 11 to r = 3, p = 13 to r = 2) | `theoremF_deep_direct_sweep2.txt` |
| `theoremF_framing_tests.py` | Theorem F §7: Lemma 3, Lemma 6, the Theorem for ten triples, instance identities | `theoremF_framing_tests.txt` |
| `theoremF_p3_blocks.py` | exploration: where the aggregate cancellation at p = 3 happens | `theoremF_p3_blocks.txt` |
| `theoremF_p3_c0_and_lift.py` | Theorem F₃: the class 3 \| c at r = 1 and the r ≥ 2 lift of g | `theoremF_p3_c0_and_lift.txt` |
| `theoremF_p3_cartier_test.py` | Theorem F₃: the exact-form mechanism at r = 1 (Q ≡ D(L/(ψ−c)) over F_3) | `theoremF_p3_cartier_test.txt` |
| `theoremF_p3_conjecture_check.py` | Theorem F₃(ii) for r ≤ 4, m ≤ 8 | `theoremF_p3_conjecture_check.txt` |
| `theoremF_p3_effective_quadratic.py` | exploration: the effective quadratic bound fails at p = 3 | `theoremF_p3_effective_quadratic.txt` |
| `theoremF_p3_proof_checks.py` | Theorem F₃ Remark 4: (V1)–(V4) | `theoremF_p3_proof_checks.txt` |
| `theoremF_p3_r1_formula.py` | Theorem F₃: the finite-field reduction at r = 1 | `theoremF_p3_r1_formula.txt` |
| `theoremF_p3_sweep.py` | Theorem F §0, §6 and Theorem F₃ Observation: which (a,b,c) satisfy the 3^{3r} tower | `theoremF_p3_sweep.txt` |
| `theoremF_p3_terms.py` | Theorem F §6: quadratic, cubic and higher parts of exp(NL) − 1 at p = 3 | `theoremF_p3_terms.txt` |
| `theoremF_shifted_probe.py` | negative result: no shifted towers for the univariate Theorem F sequences | `theoremF_shifted_probe.txt` |
| `unit_product_principle.py` | A364175/A364178: Lemmas A, B, the exact ratio identities, integrality sweeps (§1, §3) | `unit_product_principle.txt` |
