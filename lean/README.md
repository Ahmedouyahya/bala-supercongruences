# Lean 4 + Mathlib project `BalaProofs`

Toolchain `leanprover/lean4:v4.35.0` (`lean-toolchain`); Mathlib at the revision pinned in `lake-manifest.json` (`aa35a481e5f0cdb3b04a899ead15d6ca7305a624`). The build directory `.lake/` (several GB) is not included; `lake` recreates it. Do not run `lake update`: `lakefile.toml` names Mathlib's `master` branch, and the manifest pins the revision that was used.

## Build

From this directory:

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the prebuilt Mathlib for the pinned revision (otherwise Mathlib is compiled from source, which takes hours). `lake build` compiles every module of the library (`globs` in `lakefile.toml`); "Build completed successfully" with no `sorry` warning is a pass. A single entry can be built with `lake build BalaProofs.A361711`. The entry modules cannot be imported into one file, because several of them define a top-level `a`, as their benchmark statements do.

The axioms used by a theorem are printed by a file such as

```
import BalaProofs.A361711
#print axioms A361711_conjecture
```

compiled with `lake env lean <file>` after the build. For every final theorem below the result is `[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no added axiom, no `Lean.ofReduceBool` (that is, no `native_decide`).

## The twelve entries

Each final theorem is the benchmark statement from `statements/lean-targets/`, with its definitions and statement copied verbatim (checked by `verification/lean-statement-check/`). The full record of each check, with the benchmark checker Comparator and the controls, is in `verification/lean-checks/`.

| Entry | Final theorem (module) | Main supporting modules | Uses Epoch AI's | Record |
|---|---|---|---|---|
| A333561 | `oeis_333561_conjecture` (`A333561`) | `TFSetup`, `TFFrob`, `TFHarmonic`, `TFEps`, `TFLift`, `TFMain` (Theorem F), `TFInst`, `A333561Main` | `EpochA333042` | `TheoremF-A333561-A333562-A352373/` |
| A333562 | `oeis_333562_conjecture_0_congruence` (`A333562`) | Theorem F modules, `A333562Ident`, `A333562Main` | `EpochA333042` | same |
| A352373 | `oeis_a352373_supercongruence` (`A352373`) | Theorem F modules, `A352373Main` | `EpochA333042` | same |
| A333565 | `oeis_A333565_conjecture_strong_gauss_congruence` (`A333565`), all p ≥ 3 | Theorem F modules; `TF3Harm`, `TF3G`, `TF3Exp`, `TF3Main` (Theorem F₃ for (2,−1,1)); `A333565Bridge`, `A333565Main` | `EpochA333042` | `A333565/` |
| A352275 | `u_m_supercongruence_conjecture` (`A352275`), every u_m | — | `EpochA333096` | `A352275/` |
| A361711 | `A361711_conjecture` (`A361711`) | `ClosedForm`, `ProductSplit`, `InvSquares`, `UnitSquares`, `UnitSquaresCore` | — | `A361711-A364175-A364178/` |
| A364175 | `oeis_364175_conjecture_0` (`A364175`) | `BlockProduct`, `FactorialSplit`, `FloorCounting`, `GammaShift`, `UnitProduct`, `UnitSums` | — | same |
| A364178 | `oeis_364178_conjecture_0` (`A364178`) | same as A364175 | — | same |
| A386548 | `oeis_A386548_supercongruence_conjecture` (`A386548`) | `A386548Series`, `A386548Padic`, `A386548Main` | `EpochA361883` | `A386548/` |
| A363983 | `oeis_A363983_conjecture_supercongruence` (`A363983`) | `OSSLib`, `A363983Rec`, `A363983Lemmas`, `A363983Main` | `EpochA361883` (through `A386548Padic`) | `A363983/` |
| A376462 | `oeis_376462_conjecture_0` (`A376462`), both congruences | `OSSLib`, `A376462Rep`, `A376462Kernel`, `A376462Classes`, `A376462First`; `ShiftLibProd`, `ShiftLibHarm`, `ShiftLibBlock`, `A376462Shift*` | `EpochA361883` (through `OSSLib`) | `A376462/` |
| A370092 | `oeis_370092_conjecture_0` (`A370092`) | `A370092Formula`, `A370092Odd`, `A370092Two` (an elementary proof of the 2-adic lemma; Amice's theorem is not used) | — | `A370092/` |

Also proved: `A333561Oeis.aOEIS_supercongruence`, the same congruence for A333561 in Bala's own form a(n) = Σ_{j ≤ 2n} 2^j C(n+j−1, j), which differs in form from the benchmark's definition (`BinomIdent` proves the two equal).

## Bala's general conjectures (A352373, A333715)

`BalaGeneral.lean` proves, for primes p ≥ 5, two general conjectures that Bala states in comments on OEIS A352373 and A333715: `bala_A352373_general` (a(r,s;n) = [x^n]((1+x)^r(1−x)^s)^n, all integers r, s) and `bala_A333715_general` (a(r,s,n) = [x^(rn)]((1+x)/(1−x))^(sn), r ≥ 0, s any integer). (1+x)^t for an integer t is Mathlib's `PowerSeries.binomialSeries`. The module also proves `coeffPow_eq_A`: [x^(cN)]((1+x)^a(1−x)^b)^N equals Theorem F's `TF.A a b c N` for all integers a, b. `BalaGeneralCheck.lean` shows that `aRS (-1) (-3)` is the benchmark's A352373. There is no benchmark statement for these conjectures; record: `verification/lean-checks/BalaGeneral/`.

`TF.theoremF` (`TFMain`) is Theorem F at primes p ≥ 5 for all integers a, b and every c ≥ 0: |A(pM) − A(M)|_p ≤ p^{−3(1+v_p(M))}, where A(N) is defined in Lean (`TFSetup`) as the coefficient of x^{cN} in exp(N·(a·log(1+x) + b·log(1−x))), a power series over ℚ. That this coefficient equals [x^{cN}]((1+x)^a(1−x)^b)^N is proved in Lean for all integers a, b (`BalaGeneral.coeffPow_eq_A`); the entries use the earlier instance formulas of `TFInst` ((m, −1) for m ≥ 0, and (−1, −3)).

## Files from other sources

`EpochA333096.lean`, `EpochA361883.lean` and `EpochA333042.lean` are the work of Epoch AI (accepted proofs from the OEIS Open evaluation), used with Epoch AI's permission on the condition that they are credited; each header lists the changes made for Lean v4.35.0. Sources and hashes: `verification/lean-checks/EPOCH-FILES.md`. The definitions and statements copied from the benchmark files carry the Formal Conjectures copyright notice in their headers (Apache License 2.0). No other file contains code from an external repository. Licences: `NOTICE`.

## Note on the docstrings

Some docstrings refer to the proof notes by their former names under `notes/` (for example `notes/A361711-proof.md`, now `proofs/A361711.md`); `proofs/README.md` maps each note to its current file.
