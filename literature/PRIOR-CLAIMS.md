# Earlier claims on the twelve entries

Checked 2026-10-16, and re-checked 2026-10-19 (HEAD still e6955c6a; the four family rows below were added on the re-check, the earlier table had omitted them), against the public repository https://github.com/rbajaj5/a183068-supercongruence (commit e6955c6a). That repository has no licence file; its own status label for these results is "complete unchecked proof candidate" (no peer review, no machine check). Dates are the first commit of each file. The OEIS Open evaluation of Epoch AI recorded no accepted proof for any of the twelve entries.

| Entry | Earlier claim | File in `related-results/` | First committed |
|---|---|---|---|
| A352373 | cubic tower for p ≥ 5, named, together with the two-parameter family | `CoefficientFramingCubicTower.md` | 2026-07-30 |
| Theorem F family [x^{cN}](1+x)^{aN}(1−x)^{bN} | cubic tower for p ≥ 5, uniform modulus 3^(3r−1) at p = 3 | `CoefficientFramingCubicTower.md`, `BalaAugustCoefficientPacket.md` | 2026-07-30, 2026-08-11 |
| A333562 | cubic tower for p ≥ 5, named | `BalaAugustCoefficientPacket.md` | 2026-08-11 |
| A333565 | cubic tower for p ≥ 5 only, named; Bala's case p = 3 is not claimed | `BalaAugustCoefficientPacket.md` | 2026-08-11 |
| A333561 | covered as the case c = 2 of the family S_c, not named | `BalaAugustCoefficientPacket.md` | 2026-08-11 |
| A364175 | cubic tower, given Radcliffe's integrality, named | `RationalGammaRatioCubicTowers.md` | 2026-08-01 |
| A364178 | integrality and cubic tower, listed as the half-index variant of A295470 (A364178(n) = A295470(n/2), as the OEIS entry of A364178 states) | `BoberSporadicFactorialRatioPacket.md`, `BoberHalfIndexIntegralityTheorem.md` | 2026-08-13 |
| A364179 (by-product here) | integrality and cubic tower, listed as the half-index variant of A295471 | same | 2026-08-13 |
| A103885 (not one of the twelve; a case of Bala's conjecture on A333715, proved here for p ≥ 5) | cubic tower | `BalaAugustCoefficientPacket.md` | 2026-08-11 |
| Family A364172–A364184 (our Theorem U) | the p^{3r} towers of all thirteen entries reduced to integrality, by the same rational gamma-ratio transfer ("automatic once its values are known to be integral", §5) | `RationalGammaRatioCubicTowers.md` | 2026-08-01 |
| A364173 (sibling, not one of the twelve) | integrality and tower | `A364173IntegralHalfBinomialTower.md` | 2026-07-30 |
| A364176 (sibling) | integrality (affine Landau) and cubic tower | `A364176AffineLandauTower.md` | 2026-08-05 |
| A364183 (sibling) | integrality and cubic tower | `A364183AffineLandauTower.md` | 2026-08-12 |

Not claimed in that repository (searched by A-number and by parent sequence on 2026-10-16): A333565 at p = 3, A352275, A361711, A363983, A376462 (either congruence), A386548, A370092, the integrality of A364172. For A386548 the proof here adapts, with signs, the argument of `MixedStepCoefficientQuadraticTower.md` (A246437, first committed 2026-08-12).

What this repository adds for the entries above: complete written proofs checked as described in `verification/VERIFY.md`, and machine-checked Lean 4 proofs of all of them (since 2026-10-16; for A364175 and A364178 the integrality is included). The proofs of Theorem F were written after reading those drafts and follow the same strategy (reduced logarithm, quadratic estimate).

## Literature check of 2026-10-16 (night) — details in `literature/NOVELTY-CHECK-2026-10-16.md`
- Theorem F is known for c = a (and c = b) by A. Straub, Algebra & Number Theory 8 (2014), Thm 3.2(b); the instances A333561, A333562, A352373, A119259 (A333565) have c ∉ {a, b} and are not covered. The towers of A002003, A156894 and A234839 are known (Straub; Osburn et al.), so they are not by-products of this work.
- A333565 = 2·A119259 − (−1)^n is an OEIS formula line without proof (Bala, 2020); it is proved here.
- Kazandzidis's congruence is formalised in Lean elsewhere (Epoch AI's A141057 run; VictorLiwentao/lean-oeis-proofs).
- No earlier proof of any of the twelve was found other than rbajaj5's drafts; VictorLiwentao/lean-oeis-proofs (Wentao Li) contains none of the twelve.
