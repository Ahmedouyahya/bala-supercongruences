# Supercongruences conjectured by Peter Bala: proofs for twelve OEIS sequences

This repository proves the conjectures that Peter Bala posted on the OEIS entries A333561, A333562, A333565, A352275, A352373, A361711, A363983, A364175, A364178, A370092, A376462 and A386548 (statements, definitions and OEIS links: `statements/STATEMENTS.md`; the benchmark's formal statements: `statements/lean-targets/`). Each is proved as Bala stated it, and each is also proved in Lean 4 with Mathlib, as stated in the benchmark's formal statements (see Verification): the supercongruences a(n·p^k) ≡ a(n·p^(k−1)) (mod p^(3k)) for all primes p ≥ 5 and all n, k ≥ 1 on A333561, A333562, A352373, A363983, A364175, A364178 and A352275 (together with the whole family u_m to which A352275 belongs); the same congruences for all primes p ≥ 3 on A333565; a(p^k) ≡ a(p^(k−1)) (mod p^(3k)) for p ≥ 5 on A361711; both congruences a(n·p^r) ≡ a(n·p^(r−1)) and a(n·p^r − 1) ≡ a(n·p^(r−1) − 1) (mod p^(3r)) for p ≥ 5 on A376462; the congruences modulo p^(2k) for p ≥ 5 on A386548; and, on A370092, that a(n) mod k is eventually periodic with period dividing φ(k) for every k > 2. By-products (written proofs, not machine-checked unless stated): A364178 and the siblings A364172 and A364179 are integer sequences, which the OEIS entries state only conjecturally (for A364178 and A364179 unreviewed proofs were posted earlier; see below); Theorem F gives the cubic tower for the whole family [x^{cN}]((1+x)^a(1−x)^b)^N at every prime p ≥ 5 (machine-checked; the case c = a, and by symmetry c = b, is a special case of Straub 2014, Theorem 3.2(b)), with an exact classification of the residue classes (a, b, c) for which it also holds at p = 3; an order-3 recurrence for A376462; and two repairs to printed arguments in Beukers (1985). Machine-checked as well: two general conjectures that Bala states in comments on OEIS A352373 (a(r,s;n) = [x^n]((1+x)^r(1−x)^s)^n for all integers r, s) and A333715 (a(r,s,n) = [x^(rn)]((1+x)/(1−x))^(sn)), for primes p ≥ 5, as corollaries of Theorem F (`verification/lean-checks/BalaGeneral/`); with them the conjectures carried by A333715, A348410 and A351857 hold for p ≥ 5 (these sequences are a(r,s;n) or a(r,s,n) by their definitions), and so do those of A091527 and A119259 given the formula a(n) = [x^n]((1+x)^3/(1−x))^n, resp. [x^n]((1+x)^2/(1−x))^n, stated on those entries and checked here numerically, not proved (the cases r = 1 or s = 1, such as A156894, are Straub's).

## Earlier claims

Before this work, proofs for six of the twelve entries were claimed in the public drafts of rbajaj5 (repository `rbajaj5/a183068-supercongruence`, July–August 2026; by its own label unreviewed, with no machine check): A352373; A333562; A333565 for p ≥ 5; A333561, as an unnamed case of the same family; the tower of A364175, given Radcliffe's integrality; and the integrality and tower of A364178, as the half-index case of A295470. The same drafts claim the family theorem behind Theorem F for p ≥ 5, with the weaker modulus 3^(3r−1) at p = 3. For these entries this repository gives complete written proofs, checked as described in `verification/VERIFY.md`, and machine-checked Lean proofs; the proofs of Theorem F were written after reading those drafts and follow the same strategy. Not claimed there: A333565 at p = 3 with the exact rule at the prime 3 (Theorem F₃), A352275, A361711, A363983, A376462 (both congruences), A386548 and A370092. Sources, files and dates: `literature/PRIOR-CLAIMS.md`.

## Results

| Item | Statement | Method | Status | File |
|---|---|---|---|---|
| A333561 | a(n) = Σ_{j=0}^{2n} C(n+j−1,j)·2^j; a(np^k) ≡ a(np^{k−1}) (mod p^{3k}), p ≥ 5 | Theorem F, instance (a,b,c) = (3,−1,2): reduced logarithm and a quadratic estimate for Wolstenholme-type sums over units; also at p = 3 by Theorem F₃ | proved; machine-checked for p ≥ 5 (benchmark form and Bala's own form); earlier unreviewed claim: rbajaj5 | `proofs/TheoremF-p-ge-5.md`, `proofs/TheoremF-p-eq-3.md` |
| A333562 | a(n) = Σ_{j=0}^{3n} C(n+j−1,j)·2^j; a(np^k) ≡ a(np^{k−1}) (mod p^{3k}), p ≥ 5 | Theorem F, instance (4,−1,3); also at p = 3 by Theorem F₃ | proved; machine-checked for p ≥ 5; earlier unreviewed claim: rbajaj5 | `proofs/TheoremF-p-ge-5.md`, `proofs/TheoremF-p-eq-3.md` |
| A333565 | o.g.f. (1+4x)/((1+x)√(1−8x)); a(np^k) ≡ a(np^{k−1}) (mod p^{3k}), p ≥ 3 | A333565(n) = 2·A_{(2,−1,1)}(n) − (−1)^n; Theorem F for p ≥ 5, Theorem F₃ (exact-form identity and an identity in F_3[[y]]) for p = 3 | proved; machine-checked for all p ≥ 3; earlier unreviewed claim for p ≥ 5: rbajaj5 | `proofs/TheoremF-p-ge-5.md`, `proofs/TheoremF-p-eq-3.md` |
| A352373 | a(n) = [x^n] (1/((1−x)²(1−x²)))^n; a(np^k) ≡ a(np^{k−1}) (mod p^{3k}), p ≥ 5 | Theorem F, instance (−1,−3,1) | proved; machine-checked; earlier unreviewed claim: rbajaj5 | `proofs/TheoremF-p-ge-5.md` |
| A352275 and every u_m | u_m(n) = Σ_{k=0}^{mn} n/(n+2k)·C(n+2k,k) (A352275 is m = 2); u_m(np^r) ≡ u_m(np^{r−1}) (mod p^{3r}), p ≥ 5 | corollary of the machine-verified lemma `FNat_scale_supercongruence` (two-parameter scaling of truncated Catalan powers) in the Epoch/OEIS Open Lean proof of A333096 | proved and machine-verified (Lean 4 + Mathlib; `verification/lean-checks/A352275/README.md`) | `proofs/A352275-u_m-family.md` |
| A361711 | a(n) = Σ_{k=0}^{n−2} (−1)^k C(n,k)² C(n−2,k); a(p^k) ≡ a(p^{k−1}) (mod p^{3k}), p ≥ 5 | closed form a(2n+1) = (−1)^n C(3n+1,n)C(2n,n) (Zeilberger certificate); exact identity a(p^k)/a(p^{k−1}) = Π_{u<p^k/2, p∤u}(1 − p^{2k}/u²); Σ_U 1/u² ≡ 0 (mod p^k) | proved and machine-verified (Lean 4 + Mathlib) | `proofs/A361711.md`, `lean/BalaProofs/A361711.lean` |
| A363983 | a(n) = Σ_k (−1)^{n+k} C(n,k) C(n+k−1,k) C(2k,n); a(mp^r) ≡ a(mp^{r−1}) (mod p^{3r}), p ≥ 5 | adaptation of the Osburn–Sahu–Straub proof of their Theorem 1.2 | proved; machine-checked | `proofs/A363983.md` |
| A376462 | a(n) = Σ_k C(n,k)² C(n+k,k) A108625(n,n−k); a(mp^r) ≡ a(mp^{r−1}) and a(mp^r−1) ≡ a(mp^{r−1}−1) (mod p^{3r}), p ≥ 5 | first congruence: Osburn–Sahu–Straub template with two singly-unscaled classes; shifted congruence: Beukers' 1985 block induction extended to the two-index sum | proved (both congruences, all r ≥ 1); machine-checked | `proofs/A376462-first-congruence.md`, `proofs/A376462-shifted-congruence.md` |
| A364175 | a(n) = (6n)!(2n/3)!/((3n)!(2n)!(5n/3)!); integral (Radcliffe 2026, re-derived); a(np^r) ≡ a(np^{r−1}) (mod p^{3r}), p ≥ 5 | unit-product principle (Jacobsthal's method) with exact ratio identities | proved and machine-verified (Lean 4 + Mathlib); earlier unreviewed claim: rbajaj5 | `proofs/A364175-A364178.md`, `lean/BalaProofs/A364175.lean` |
| A364178 | a(n) = (10n)!(3n)!(n/2)!/((6n)!(5n)!(3n/2)!n!); integral; a(np^r) ≡ a(np^{r−1}) (mod p^{3r}), p ≥ 5 | integrality by Legendre's formula; unit-product principle | proved and machine-verified (Lean 4 + Mathlib); earlier unreviewed claim: rbajaj5 (as A295470 at n/2) | `proofs/A364175-A364178.md`, `lean/BalaProofs/A364178.lean`; siblings A364172, A364179 in `proofs/A364172-A364179-integrality.md` |
| A386548 | a(n) = [x^n] ((1−x)/(1−x+x²))^n; a(np^k) ≡ a(np^{k−1}) (mod p^{2k}), p ≥ 5 | elementary: Kazandzidis's congruence in quotient form and divisibility synchronisation (adapted from rbajaj5's A246437 argument) | proved (exponent 2k is sharp); machine-verified (Lean 4 + Mathlib; `verification/lean-checks/A386548/README.md`) | `proofs/A386548.md` |
| A370092 | a(n) mod k eventually periodic with period dividing φ(k), k > 2 | Stirling expansion; Kallat's argument with p-integral coefficients for odd prime powers; a 2-adic Stirling lemma for powers of two (via Amice's theorem in the written proof; elementary in the Lean proof) | proved (φ(k) is sharp); machine-checked (sharpness not formalised) | `proofs/A370092.md` |

`proofs/README.md` gives, for every item, the verification pointers (scripts, outputs, review reports).

## Verification

All twelve conjectures are proved in Lean 4 with Mathlib, exactly as stated in the benchmark's formal statements (`statements/lean-targets/`), with only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Each proof was also accepted by the benchmark's checker Comparator against the official challenge file, with Lean's kernel and with the independent kernel nanoda, and a true but weaker statement was rejected for every entry. The protocol is `verification/lean-checks/PROTOCOL.md`; the record of each entry is in `verification/lean-checks/`; `verification/lean-statement-check/` checks that the repository's definitions and statements are the benchmark's. Whether each benchmark statement says what Bala conjectured is a question for a human reader: `verification/STATEMENT-SHEETS.md` puts each one next to Bala's text.

`verification/VERIFY.md` describes the other evidence and how to re-run it: theorem-level numerics (each statement tested from its OEIS definition in exact arithmetic), proof-level numerics (every lemma of each written proof recomputed by independent scripts), and independent review reports (`verification/referee-reports/`, with the disposition of every finding in `DISPOSITIONS.md`). These matter for the results that are not formalised: Theorem F₃ beyond the instance used for A333565, Theorem U and the family A364172–A364184, and the by-products and sharpness claims.

## Repository layout

- `proofs/` — one note per item: statement, lemmas, proof, computer checks, references (`proofs/README.md` is the index).
- `statements/` — `STATEMENTS.md` (definitions, formulas, conjecture text and links from the OEIS, 2026-10-15), `oeis_bala_records.json` (the stored OEIS records) and `lean-targets/` (the benchmark's formal statements, from Formal Conjectures).
- `numerics/` — `scripts/` (Python and Maxima), `out/` (archived outputs), `data/` (OEIS terms used by the scripts), `README.md` (which script tests which theorem or lemma).
- `lean/` — the Lean 4 + Mathlib project `BalaProofs` (`lean/README.md`).
- `verification/` — `VERIFY.md`, `lean-checks/` (the machine checks), `lean-statement-check/`, `STATEMENT-SHEETS.md`, `referee-reports/`.
- `literature/` — literature list, the digest of Beukers (1985), the novelty check, earlier claims (`PRIOR-CLAIMS.md`), the download list of the papers used (PDFs not redistributed).
- `paper/` — the Typst sources of the paper draft (`paper/README.md`: how to build).
- `LICENSE`, `NOTICE`, `LICENSES/` — licences (see below).

## How to reproduce

Python (needs `sympy` for the symbolic checks), from the repository root:

```
python3 -I numerics/scripts/<name>.py
```

`numerics/README.md` lists every script with the theorem or lemma it tests and its output file, and says where each script writes. The Zeilberger certificate for A361711 is produced by `maxima -b numerics/scripts/a361711_zeilberger.mac`.

Lean (Lean v4.35.0 and the Mathlib revision pinned in `lean/lake-manifest.json`):

```
cd lean
lake exe cache get
lake build
```

`lake exe cache get` downloads the prebuilt Mathlib for the pinned revision (without it Mathlib is compiled from source, which takes hours); `lake build` then compiles every module. "Build completed successfully" with no `sorry` warning is a pass; `lean/README.md` says how to print the axioms of each final theorem.

## Authors

Mohamed Vadel Hadweni (ORCID 0009-0000-0713-339X) and Ahmedou Yahye Gleiguem Kheyri (ORCID 0009-0006-6390-4420).

Computations, literature search, drafting and the Lean formalisation were carried out with computer assistance (Python with sympy and mpmath, Maxima, Lean 4 with Mathlib, and an AI assistant, Claude by Anthropic); the review reports in `verification/referee-reports/` were produced by language models and are labelled as such. Every mathematical statement in this repository was checked as described in `verification/VERIFY.md`.

Conjectures: Peter Bala (OEIS). Methods adapted are credited in each note (the Epoch/OEIS Open machine proof of A333096, Osburn–Sahu–Straub, Beukers, Straub, Kallat, Radcliffe, Cai, Robert–Zuber, Amice/Colmez, and the unreviewed drafts of rbajaj5). Earlier claims on these entries are listed in `literature/PRIOR-CLAIMS.md`. Three Lean files are the work of Epoch AI, from its OEIS Open evaluation: the accepted proofs of A333096 (`lean/BalaProofs/EpochA333096.lean`, used for A352275), A361883 (`EpochA361883.lean`, Kazandzidis's congruence, used for A386548, A363983 and A376462) and A333042 (`EpochA333042.lean`, the power-series exponential and Dwork's lemma, used for Theorem F). They are included, adapted to Lean v4.35.0, with Epoch AI's permission, on the condition that they are credited to Epoch AI (`verification/lean-checks/EPOCH-FILES.md`). The benchmark statements are from Formal Conjectures and Epoch AI's LeanOpenProblems.

## Licence

The authors' code is licensed under the Apache License 2.0 (`LICENSE`) and their text under CC BY 4.0. Material from Formal Conjectures, LeanOpenProblems, Epoch AI and the OEIS keeps its own terms; `NOTICE` says which files are which.

## Status

Not yet submitted anywhere; nothing here has been posted to the OEIS or arXiv.
