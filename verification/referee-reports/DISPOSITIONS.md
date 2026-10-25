# Dispositions of the review findings

This file records what happened to every finding of the review reports in this folder. The reports were produced by automated reviewers (language models, named in each file name) on 2026-10-15, from the proof notes as they stood at the time; they are kept verbatim as evidence, not as authority, and a finding listed here is a statement of the report, not an established defect. The outcomes are those recorded on 2026-10-15 and 2026-10-16 in the project's working log (not part of this repository) and in `verification/VERIFY.md` §7; this file was written on 2026-10-16. Conventions:

- **Findings.** A finding is every item a report flags as ERROR, GAP or UNCLEAR, every defect it asserts elsewhere in its text, and every "least sure" step that names a missing or unclear argument. In the re-review (REREVIEW) reports, findings are the confirmed errors (labels E1, E2, … as in the reports), the citation mismatches (C), the unverified concerns that point at a citation without a backing file (U) and the exposition items (X), numbered here in the order in which they appear in each report section; S marks a side remark inside a report's "suspected then cleared" list. Items a report clears itself, and items that only say what the reviewer did not check, are listed after each table, not as rows.
- **Outcomes.** "fixed in …" (the record names the change), "reviewer error: …", "not applicable: …", "no change: …", or "outcome not recorded". After "outcome not recorded", a sentence starting "Current text" describes the note as of 2026-10-16; it describes the file, not a recorded response to the finding.
- **Paths.** The reports cite notes under `notes/` and scripts under `numerics/`; the current files are `proofs/…` (table in `README.md` of this folder) and `numerics/scripts/…`, with outputs in `numerics/out/`. Section and lemma numbers in this file refer to the current notes; several reports cite line numbers of the versions they read.
- All twelve entries were later proved in Lean; see the last section.

## Cross-model reports (review instruction: `PROMPT.txt`)

### `A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt`

Note: `proofs/A352275-u_m-family.md`. Verdict: CORRECT WITH FIXES. Numbering (1)–(4) as in the report's summary; L1–L2 from its list of least-sure steps.

| Finding | Outcome | Evidence |
|---|---|---|
| (1) GAP: the result rests on `FNat_scale_supercongruence`, which the note does not prove; the note is a conditional reduction, and the unqualified "proved" in its header overstates it. | no change: the note is by design a corollary of the machine-verified lemma and does not re-prove it. The lemma's file was later compiled and included (`lean/BalaProofs/EpochA333096.lean`), and the corollary was proved in Lean on 2026-10-16. | `proofs/A352275-u_m-family.md` §2, §5; `lean/BalaProofs/A352275.lean`; `verification/lean-checks/A352275/README.md` |
| (2) GAP: §4 uses an undefined v; with v = v_p(N) the inequality fails (p = 5, S = 11, N = 10 gives valuation 4 < 6). | fixed in `proofs/A352275-u_m-family.md` §4 (v := min(v_p(N), v_p(S−N)); the report's example is quoted to show that the definition matters). | `numerics/out/rereview_short_A352275.txt` |
| (3) UNCLEAR: the remark in the Corollary's proof says "the theorem quantifies n, r > 0", which contradicts the Theorem's quantifiers (N ≥ 1, r ≥ −N). | fixed in `proofs/A352275-u_m-family.md` §1 (the remark now says that the Corollary quantifies n ≥ 1, so that N ≥ 1 and r ≥ 1 in the application of the Theorem). | `proofs/A352275-u_m-family.md` §1 |
| (4) UNCLEAR: the identification of the benchmark's floor/`toNat` definition of u_m with T(n, mn) is asserted, not verifiable from the text. | outcome not recorded. The identification was later proved in Lean as part of the proof of the benchmark statement (bridge u_m(n) = FNat((2m+1)n, mn)). | `lean/BalaProofs/A352275.lean`; `verification/lean-checks/A352275/README.md` |
| L1–L2: the reviewer could not inspect the Lean source, so the faithfulness of the quoted lemma statement and its behaviour at Y = 0 (r = −N) could not be confirmed. | no change: the re-review compared the quoted names, statements and line numbers with `Spec.lean` and found them verbatim; the file was compiled on 2026-10-16 in Lean v4.27.0 and v4.35.0. The Y = 0 point is not separately recorded. | `REREVIEW-A352275-and-A361711--fact-only-agent.txt` (citation audit); `verification/VERIFY.md` §5 |

The report found no ERROR. Its least-sure step 3 is finding (2).

### `A361711-proof--nemotron-3-ultra-free.txt`

Note: `proofs/A361711.md`. Verdict: CORRECT WITH FIXES. Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (§1, Lemma 1) GAP: the telescoping boundary value G(n, n+1) := 0 is defined and checked afterwards rather than derived; the repair of the boundary is not marked; the recurrence rests on a computer-verified Zeilberger certificate. | outcome not recorded (the boundary repair itself had been made before this report, in the review round without archived reports, see below). Lemma 1 was later proved in Lean, including the certificate identities. | `proofs/A361711.md` §1; `numerics/out/rereview_short_A361711.txt`; `lean/BalaProofs/ClosedForm.lean` (`Bala.aQ_odd`) |
| F2 (§3, Lemma 3) UNCLEAR: the step Σ 1/v² ≡ Σ v² (mod p^k) ("inversion permutes the units") is too terse. | fixed in `proofs/A361711.md` §3 (the inversion step is spelled out). | `proofs/A361711.md` Lemma 3 |
| F3 (§3, proof of the Theorem) GAP: a(M′) ≠ 0 is used without proof. | fixed in `proofs/A361711.md` §3 (cited to Lemma 1: a(M′) = ±C(3n′+1,n′)C(2n′,n′)). | `proofs/A361711.md` §3 |
| L3: the integrality of the elementary symmetric functions e_j in the expansion of (★) is not argued. | fixed in `proofs/A361711.md` §3 (e_j described as sums of products of p-adic units, hence p-adic integers). | `proofs/A361711.md` §3 |

Least-sure steps 1 and 2 are F1 and F2.

### `A363983-proof--nemotron-3-ultra-free.txt` (truncated run)

Note: `proofs/A363983.md`. No verdict (the output stops mid-sentence). Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (Lemma 6) GAP: the claim that replacing each kernel D by its lower-level value yields exactly Σ_{s+1} is not justified (the explanation is cut off). | fixed in `proofs/A363983.md` Lemma 6 (the regrouping is written out). | `numerics/out/rereview_oss_a363983.txt` (Lemma 6 internals) |

Every other section of this run reports "no issue found".

### `A363983-proof--nemotron-3-ultra-free--rerun.txt`

Note: `proofs/A363983.md`. Verdict: CORRECT WITH FIXES.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (Lemma 5) GAP: the valuation equalities assume p ∤ m, which the Theorem does not state. | fixed in `proofs/A363983.md` §0 notation (p ∤ m assumed, with the reduction (m, r) → (m′, r + e)). | `numerics/out/rereview_oss_a363983.txt` (m = p, 2p) |
| F2 (Lemma 6) UNCLEAR: the regrouping to Σ_{s+1} is terse. | fixed in `proofs/A363983.md` Lemma 6 (the regrouping is written out). | `proofs/A363983.md` Lemma 6 |
| L3: the Q₂ identity C(N+K−1,K)/C(M+K′−1,K′) = C(N+K,K)/C(M+K′,K′) is compressed. | outcome not recorded. | `numerics/out/rereview_oss_a363983.txt` (Q₂ rewriting exact in all cases) |

Least-sure steps 1 and 2 are F1 and F2.

### `A364175-A364178-factorial-ratio-towers--nemotron-3-ultra-free.txt`

Note: `proofs/A364175-A364178.md`. Verdict: CORRECT WITH FIXES. Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (§1, Theorem 2) UNCLEAR: the definition of F(x) contains −⌊x⌋, and the coefficient count 10+3−6−5−1−1 = 0 mixes the floors with N_k. | fixed in `proofs/A364175-A364178.md` §1 (floor bookkeeping clarified in a parenthesis after the display). | `numerics/out/rereview_quad_factorial_identities.txt` |
| F2 (§2, Lemma A) GAP: relies on Lemma 2 of the Theorem F note (S₁ ≡ 0 mod p^{2r}, S₂ ≡ 0 mod p^r), which was not in the reviewer's directory. | not applicable: the lemma is Lemma 2 of `proofs/TheoremF-p-ge-5.md`, present in the project but not supplied to the reviewer. | `proofs/TheoremF-p-ge-5.md` §2; `numerics/out/rereview_quad_factorial_congruences.txt` |
| F3 (§2, Lemma B) GAP: same dependency as F2. | not applicable: as F2. | as F2 |
| L3: the derivation of the exact ratio identities of Theorem 3 skips the cancellation of the powers of p. | outcome not recorded. Current text: §3 contains a "Derivation for b" paragraph that states the cancellation of the powers of p and of 2. | `numerics/out/rereview_quad_factorial_identities.txt` (F9/F10) |

Least-sure step 1 is F2. Least-sure step 2 (the bound q^k ≤ 3ρ when ε_k = 1) is stated by the report to be correct.

### `A370092-periodicity-proof--nemotron-3-ultra-free.txt`

Note: `proofs/A370092.md`. Verdict: CORRECT WITH FIXES. Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (§3, Lemma B) GAP: E_k and S₂ are Mahler coefficients of functions that are discontinuous on ℤ₂, so Amice's theorem (Colmez Th. I.4.7) does not apply. | reviewer error: the functions are analytic on each class mod 2, hence in LA₁ and continuous, since the classes mod 2 are open. A sentence saying so was added to `proofs/A370092.md` §3. | `numerics/out/rereview_a370092_amice.txt`; `verification/lean-checks/A370092/README.md` (the Lean proof uses an elementary proof of Lemma B instead of Amice's theorem) |
| F2 (§3, k = 15) GAP: the finite check for the exceptional k is not reproducible from the text. | fixed: self-contained script `numerics/scripts/lemmaB_k15_residue_check.py` for k ∈ {3, 6, 7, 15} (0 violations; minimum v₂(S₁) = 2, 2, 2, 9), cited in `proofs/A370092.md` §3. | `numerics/out/lemmaB_k15_residue_check.txt` |
| F3 (§4) UNCLEAR: the start index max(α_i + 1, α + 1) is one more than Proposition 1 needs for the odd prime powers. | outcome not recorded. Current text: §4 keeps max(α_i + 1, α + 1). | `numerics/out/rereview_a370092_periods.txt` |
| L3: bound (2) is stated for n ≥ m+1 while Lemma B assumes n ≥ m+2. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_a370092_lemmaB.txt` (bound (2) holds from n = m+1) |

Least-sure steps 1 and 2 are F1 and F2.

### `A376462-proof-first-congruence--nemotron-3-ultra-free.txt`

Note: `proofs/A376462-first-congruence.md`. Verdict: CORRECT WITH FIXES. The background note `proofs/A363983.md`, whose Lemmas 1–4 the note uses, was not supplied (file header); a second run with it is the next report. Numbering I1–I8 as in the report.

| Finding | Outcome | Evidence |
|---|---|---|
| I1 (Class S) GAP: the moduli taken from Lemma 1 (Kazandzidis) are not stated or proved in the document. | not applicable: Lemma 1 is stated and proved in `proofs/A363983.md`, which was not supplied to this run. | `proofs/A363983.md` Lemma 1; `numerics/out/rereview_oss_lemmas.txt` |
| I2 (Class S) GAP: the bound v_p(2M−K′−I′), v_p(M−K′−I′) ≥ min(r−1, μ−1) used for Q₄ is not justified. | outcome not recorded. | `numerics/out/rereview_oss_a376462.txt` (Q₄ ≡ 1 modulo the stated p^{r+2+2min(r−1,μ−1)}, 0 failures) |
| I3 (Class S) UNCLEAR: the convention s = ∞ for k = 0 (σ = ∞ for i = 0) would give a negative valuation bound; the zero indices should be a separate case. | outcome not recorded. Current text: §1 keeps the convention and treats k = i = 0 separately. | `numerics/out/rereview_oss_a376462.txt` (k = 0, i = 0, k = i = 0 included) |
| I4 (Lemma 7) GAP: the use of Lemma 1 for C(mp^t, pi″) modulo p^t depends on the exact statement of Lemma 1. | not applicable: Lemma 1 is in `proofs/A363983.md`, not supplied to this run. | `proofs/A363983.md` Lemma 1 |
| I5 (Class K) GAP: the use of Lemma 4(ii) for C(2N−k−pi′, N) depends on the missing note. | not applicable: Lemma 4 is in `proofs/A363983.md`, not supplied to this run. | `proofs/A363983.md` Lemma 4 |
| I6 (§5) GAP: the first-order expansions of the binomial coefficients modulo p² are not proved. | fixed in `proofs/A376462-first-congruence.md` §5 (the expansions are referred to Lemma 1.3 of the shifted-congruence note, which proves them for every r; §5 is marked as superseded). | `proofs/A376462-shifted-congruence.md` Lemma 1.3 |
| I7 (§5, class K) GAP: "Kazandzidis for the last factor" C(N+pj′−1, pj′) is applied to a binomial of the form C(pA−1, pB), not C(pA, pB). | outcome not recorded. Current text: §5 is marked as superseded by `proofs/A376462-shifted-congruence.md`. | `numerics/out/rereview_oss_a376462.txt` (§5 expansions, 0 failures) |
| I8 (§5, class J) GAP: same as I7 for C(N+pk′−1, pk′). | outcome not recorded. Current text: as I7. | as I7 |

The least-sure steps are I1, I6 and I2; the closing recommendation repeats I1 and I6.

### `A376462-proof-first-congruence--nemotron-3-ultra-free--with-background.txt`

Note: `proofs/A376462-first-congruence.md`, with `proofs/A363983.md` supplied. Verdict: CORRECT WITH FIXES.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (Class S, Q₄) GAP: the modulus is derived assuming v_p(M) = r−1 (p ∤ m); the case p ∣ m is not addressed. | fixed in `proofs/A376462-first-congruence.md` (p ∤ m without loss of generality, with the reduction to (m′, r+e), as in `proofs/A363983.md`). | `numerics/out/rereview_oss_a376462.txt` (m = p, 2p) |
| F2 (Class S, valuation of T(M;K′,I′)) GAP: the bound v_p(C(M,K′)) ≥ r−s is not justified when p ∣ m. | fixed: as F1. | as F1 |
| F3 (Lemma 7) UNCLEAR: the modulus tracking for the terms i′ = pi″ is terse. | outcome not recorded. | `numerics/out/rereview_oss_a376462.txt` (Lemma 7, 0 failures) |
| F4 (§5, classes K and J) GAP: the first-order expansions are stated without proof. | fixed in `proofs/A376462-first-congruence.md` §5 (referred to Lemma 1.3 of the shifted-congruence note; §5 marked as superseded). | `proofs/A376462-shifted-congruence.md` Lemma 1.3 |
| F5 (§5, class B) GAP: the argument that R₁ = 0 for the pairs added by completing the top blocks does not treat n′ + n″ + 1 > m separately. | outcome not recorded. Current text: §5 is marked as superseded. | `numerics/out/rereview_oss_a376462.txt` (§5 block) |
| F6 (§5, class K) GAP: H′_{k+pj′} ≡ H′_k (mod p) is used without derivation. | outcome not recorded. Current text: §5 is marked as superseded. | as F5 |
| L3: in the Lemma 7 induction, that each inner sum is p^s times a p-adic integer is not spelled out. | outcome not recorded. | `numerics/out/rereview_oss_a376462.txt` |

Least-sure steps 1 and 2 are F4 and F1.

### `A376462-shifted-congruence-proof--nemotron-3-ultra-free.txt`

Note: `proofs/A376462-shifted-congruence.md`. Verdict: CORRECT; the report states that no errors, gaps or unclear steps were found. Two remarks on wording appear inside sections that the report marks as correct:

| Finding | Outcome | Evidence |
|---|---|---|
| R1 (Lemma 2.2): the proof's "t = 0 is empty" is called imprecise (for t = 0 the claim is a congruence modulo 1). | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_shifted_harmonic.txt` |
| R2 (Lemma 2.6): "t = 0 is Lemma 2.2" is called terse. | outcome not recorded. Current text: unchanged. | as R1 |

The three least-sure steps (Lemma 2.5 on general blocks, the tight X_s step of §4 (4.b.2), and the stratification of §7 Step 3) are listed "not because of any detected flaw". The project record notes that these are the places where the replay scripts show slack 0 and pass up to r = 4 (`numerics/out/referee_B_deeper_cases.txt`, `numerics/out/referee_B_wider_primes.txt`); the later re-review cleared Lemma 2.5 on general blocks (`REREVIEW-A376462-shifted--fact-only-agent.txt`).

### `A386548-quadratic-tower-proof--nemotron-3-ultra-free.txt`

Note: `proofs/A386548.md`. Verdict: CORRECT WITH FIXES. Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (§2, (T2)) GAP: the identity C(N+k−1,k) = (N/k)·C(N+k−1,k−1) is called false. | reviewer error: the ratio C(N+k−1,k)/C(N+k−1,k−1) = (k−1)!·N!/(k!·(N−1)!) = N/k; a one-line verification was added to `proofs/A386548.md` §2. | `numerics/out/rereview_quad_A386548_identities.txt` ((T1)/(T2) identities) |
| F2 (§3, unscaled terms) GAP: inherits F1. | reviewer error: as F1. | as F1 |
| F3 (§3, case s < r−1) GAP: (T2) is said not to cover C(D−1, k′). | reviewer error: D − 1 = M + k′ − 1, so C(D−1,k′) = C(M+k′−1,k′) has the form covered by (T2); a one-line verification was added to §3. | `numerics/out/rereview_quad_A386548_identities.txt` (C(D−1,k′) identity) |
| F4 (§3, case s < r−1) UNCLEAR: the handling of the boundary pairs j′ = 0, k′ = 0 should be checked explicitly (the report then finds it correct). | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_quad_A386548_identities.txt` (I7/I10, boundary pairs) |
| L3: replacing r by R := v_p(N) throughout the proof is a notational hazard. | outcome not recorded. Current text: unchanged (§3 explains the replacement). | `numerics/out/rereview_quad_A386548_congruences.txt` (cases with p ∣ n) |

Least-sure steps 1 and 2 are F1 and F3.

### `TheoremF-coefficient-framing-proof--nemotron-3-ultra-free.txt`

Note: `proofs/TheoremF-p-ge-5.md`. Verdict: CORRECT WITH FIXES. Background notes were not supplied.

| Finding | Outcome | Evidence |
|---|---|---|
| F1 (Lemma 4): the formula for [x^T]UV is said to omit a factor (−1)^T; numerically the value is the same. | fixed in `proofs/TheoremF-p-ge-5.md` Lemma 4 (remark added: for odd T both sides vanish, so no sign factor is needed). | `numerics/out/rereview_theoremF_p5_identities.txt` (Lemma 4 formulas) |
| F2 (§4) GAP: the case c = 0 is not addressed. | fixed in `proofs/TheoremF-p-ge-5.md` §0 (sentence added: for c = 0, A(N) = 1 for every N). | `proofs/TheoremF-p-ge-5.md` §0 |
| L1 (Lemma 3(ii)): "Σ v^{−2} ≡ ½S₂" is written without its modulus. | outcome not recorded. Current text: "≡ ½ S_2 ≡ 0 (mod p^e)". | `numerics/out/rereview_theoremF_p5_valuations.txt` |
| L3 (§4, j ≥ 3): the chain v_p(j!) ≤ (j−1)/(p−1) ≤ (j−1)/4 ≤ (j−3)r is loose; a direct computation for small j would be clearer. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_theoremF_p5_valuations.txt` (j < 300, r ≤ 7) |

Least-sure step 2 (Lemma 6 at r = 2) is stated by the report to work.

### `TheoremF-p3-proof--nemotron-3-ultra-free.txt`

Note: `proofs/TheoremF-p-eq-3.md`. Verdict: CORRECT. Every section reports "no issue found"; there are no findings. The three least-sure steps (Lemma H(b), Lemma J(b), Lemma D) assert no defect. The file ends in mid-sentence.

### `TheoremF-p3-proof--deepseek-v4.1-flash-free.txt`

Note: `proofs/TheoremF-p-eq-3.md`. Verdict: CORRECT. Numbering G1–G2 as in the report.

| Finding | Outcome | Evidence |
|---|---|---|
| G1: Lemma G, the reduced-logarithm Lemma 1 and the A333565 identity are imported from the p ≥ 5 note; the F₃ identity of Lemma J is called asserted as "checked" rather than shown. | fixed in `proofs/TheoremF-p-eq-3.md` §1 (an "Imports" paragraph lists the three items taken from `proofs/TheoremF-p-ge-5.md`). The Lemma J part is not separately recorded; current text: the proof of Lemma J compares all coefficients in the text. | `proofs/TheoremF-p-eq-3.md` §1, Lemma J |
| G2: Lemma H(a) defers the integrality g_t ∈ ℤ_(3) to the proof of (b). | fixed in `proofs/TheoremF-p-eq-3.md` Lemma H (integrality is now established before it is used). | `numerics/out/rereview_theoremF_p3_lemmas.txt` (Lemma H) |
| §0: the equivalence A(3M) ≡ A(M) ⇔ A(n·3^r) ≡ A(n·3^{r−1}) is asserted, not proved. | outcome not recorded. Current text: unchanged. | `proofs/TheoremF-p-eq-3.md` §0 |

The least-sure steps (Lemma H(b) for 3 ∣ t, Lemma G, Lemma J(c)) assert no defect beyond G1.

## Re-review reports (REREVIEW)

Produced on the night of 2026-10-15 under the rule that a mistake may be reported only after an exact test reproduces it; each report's scripts are `numerics/scripts/rereview_*.py`, with outputs `numerics/out/rereview_*.txt`. The record of this round states that no mathematical error was found in any proof, and that the corrected sentences were in remarks, in citations and, in the shifted-congruence note, in one justification sentence. One rule from this round applies to several rows: checks attributed to earlier reviewers that were not archived are no longer cited.

### `REREVIEW-A352275-and-A361711--fact-only-agent.txt`

Verdict for both notes: no confirmed error.

**Note 1: `proofs/A352275-u_m-family.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| C1 (§4 bullet 1): the example p = 5, S = 11, N = 10 (valuation 4) is not in the cited output file. | fixed in §4 (the example now cites `numerics/scripts/rereview_short_A352275.py`). | `numerics/out/rereview_short_A352275.txt` |
| C2 (§4 bullet 3): "u_2 = A352275 agrees … for n ≤ 5" is not computed by the cited sweep. | fixed in §4 (now n ≤ 18 for u_2, n ≤ 22 for u_1, n ≤ 15 for u_3, cited to `rereview_short_A352275.py`; the sentence states that the sweep script does not perform this check). | `numerics/out/rereview_short_A352275.txt` |
| C3 (§2): "numerically also holds for −3N ≤ r < −N" has no file. | fixed in §2 (210 cases, 0 violations, cited to `rereview_short_A352275.py`). | `numerics/out/rereview_short_A352275.txt` |
| C4 (§5(a)): the method summary attributed to Adamczewski's Appendix A is the Sol run's own `metadata.json`; Appendix A.1 describes a different accepted run. | fixed in §5(a) (the summary is attributed to the run's `metadata.json`; Appendix A.1 is attributed to run `oeis-lite-200usd-fable-i7s7n9q7v4emgjp7`). | `proofs/A352275-u_m-family.md` §5 |
| C5, X2: the second accepted machine proof (theorem `C2`) proves the two-parameter statement for every integer S, without r ≥ −N; the note mentions only one accepted proof. | fixed in §5(a) together with C4 (the second run and its theorem `C2` are named). | `proofs/A352275-u_m-family.md` §5 |
| X1 (§4 bullet 2): "exactly 3k in most cases" is 20 of the 36 cases. | outcome not recorded. Current text: "exactly 3k in 20 of the 36 cases". | `numerics/out/sweep_2026-10-15.txt` |
| X3 (§5(a)): the run's `metadata.json` contains a model-written `full_proof` text, while the note lists "a human-readable proof of the lemma" as not done. | outcome not recorded. Current text: unchanged. | `proofs/A352275-u_m-family.md` §5 |

Not listed as rows: the cleared items of section (2) (coefficient formula for negative r, the §3 chain, β(S,N) for all S, the two-parameter congruence, the range r < −N, the Lean lemma as stated, the benchmark's `u`, the Corollary's valuations); U1 (the Lean proof was not compiled, by the review's instructions; it was compiled on 2026-10-16, `verification/VERIFY.md` §5); X4 (an informational remark on the OEIS server).

**Note 2: `proofs/A361711.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| U4: the "independent referee check (n ≤ 300, n ≤ 400, p ≤ 79 with p^k ≤ 120000)" has no file in `numerics/out/`. | fixed: the citation of the unarchived check was removed; Appendix A now cites the re-review's own checks. | `numerics/out/rereview_short_A361711.txt` |
| C1 (§2): "both identities were also checked exactly for p ≤ 47, k ≤ 4" overstates the range (cut-off p^k ≤ 60000). | fixed in §2 (now "p ≤ 47 with p^k ≤ 60000", plus the re-review's range). | `numerics/out/a361711_harmonic_reduction.txt`; `numerics/out/rereview_short_A361711.txt` |
| C2, X2: `a361711_zeilberger.mac` writes `zeil_out.txt` in the working directory, not the cited output path. | outcome not recorded. Current text: Appendix A still names `numerics/out/a361711_zeilberger_certificate.txt` as the output. | `numerics/scripts/a361711_zeilberger.mac` |
| C3 (§1): "sympy `expand` confirms identically" and "P(n,n) = …, checked symbolically" have no check in `a361711_zeilberger_check.py`, which tests the identity at integer points. | fixed in §1 (both now cite the symbolic checks of `rereview_short_A361711.py`; the sentence states that the older script tests integer points 2 ≤ n < 40). | `numerics/out/rereview_short_A361711.txt` |
| C4 (§4): "v_5(a(35) − a(7)) = 5, v_p(a(np) − a(n)) ≥ 3 …" cites no file. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_short_A361711.txt` (values verified) |
| X1 (§1): "k = n−2, n−1, n where R has poles" is inaccurate: R has poles at k = n−1, n, n+1, n+2; at k = n−2 it is G(n,k+1) that meets a pole. | outcome not recorded. Current text: "k = n−1, n, n+1, n+2 where R has poles and k = n−2 where G(n,k+1) meets one". | `proofs/A361711.md` §1 |

Not listed as rows: the cleared items of section (2); U2 (compilation and `#print axioms` not re-run, by the review's instructions; see `lean/README.md` and `verification/lean-checks/A361711-A364175-A364178/README.md`); U3 (the equation number in Zhong–Chern–Cai was not checked; the transcribed statement is numerically true and used only for by-products); U5 (the Maxima run was not reproduced; the certificate was re-verified independently).

### `REREVIEW-A386548-and-A364175-A364178--fact-only-agent.txt`

Verdict for both notes: no confirmed error.

**Note 1: `proofs/A386548.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| S1 (Remark (ii)): the sketch claims all odd primes p ∤ uv, but for p = 3 the text's (JK) does not apply (Robert–Zuber's 3² form would be needed). | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_quad_A386548_congruences.txt` (remark (ii) family) |
| U1 (§4): "the referee extended this to n ≤ 6, r ≤ 3, and to p ∣ n" refers to an unarchived check. | fixed: the reference to the earlier reviewer was removed. Current text: "(independently extended to n ≤ 6, r ≤ 3, and to p ∣ n)", without a file name. | `numerics/out/rereview_quad_A386548_congruences.txt` (n ∈ {1..6, p}, r ≤ 3) |
| U2 (§0, references): the rbajaj5 draft date "Aug 2026" is not in the local snapshot, which records only the fetch date. | outcome not recorded. Current text: unchanged. | `proofs/A386548.md` header and references |
| C1 (§1): the agreement of formula (1) with the OEIS formula is attributed to `sweep_2026-10-15.py`, which computes only the OEIS formula. | fixed in §1 (now cited to `rereview_quad_A386548_identities.py`, N ≤ 60; the sentence states that the earlier attribution was wrong). | `numerics/out/rereview_quad_A386548_identities.txt` |
| C2 (§4): "formula (1) against the OEIS values … (n ≤ 20)" is performed by no file. | fixed in §4 (now N ≤ 60, cited to `rereview_quad_A386548_identities.py`). | `numerics/out/rereview_quad_A386548_identities.txt` |
| C3 (§4): "5310 pairs per prime" is 1770 per prime (5310 in total). | fixed in §4 ("1770 pairs per prime (5310 in total)"). | `numerics/out/jk_ratio_form_and_closed_forms.txt` |
| C4 (§1): the numerics "n ≤ 3, r ≤ 2, p ∈ {5,7,11,13}" lack (p, n, r) = (13, 3, 2) in the sweep output. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_quad_A386548_congruences.txt` (case computed, v = 4) |
| X1 (§2): the level form is called "the form actually used below", but case s < r−1 uses the full asymmetric form. | outcome not recorded. Current text: "the level form used in the case s ≥ r − 1 below (the case s < r − 1 uses the full asymmetric form)". | `proofs/A386548.md` §2 |
| X2 (§1): formula (1) at N = 0 needs the convention C(−1, 0) = 1, which is not stated. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_quad_A386548_identities.txt` (I1–I3) |

Not listed as rows: the other cleared items of section (2); the remark that Robert–Zuber's bibliography cites Kazandzidis and not Jacobsthal (the report calls it immaterial).

**Note 2: `proofs/A364175-A364178.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| U3 (§3): "the referee added (11,2,3), p = 13 and p = 5, r = 3" refers to an unarchived check. | fixed: the reference to the earlier reviewer was removed. Current text: "independently also checked at (11,2,3), p = 13 and p = 5, r = 3", without a file name. | `numerics/out/rereview_quad_factorial_identities.txt` (F9/F10); `numerics/out/rereview_quad_factorial_congruences.txt` (G4) |
| C6, X3 (§1): "a(n) likewise" hides that the valuation sweep for a(n) excludes q = 3 for 120 < n ≤ 1500; the b-sweep pair count includes q = 2 for n ≤ 400. | fixed in §1 (the computer-check sentence states both restrictions). | `numerics/out/unit_product_principle.txt` |
| C7 (§1): "(Both formulas checked for n ≤ 40.)": the script range is n = 1..39. | outcome not recorded. Current text: "(Both formulas checked for 1 ≤ n ≤ 39.)". | `numerics/out/rereview_quad_factorial_identities.txt` (F3) |
| X4 (Lemma B): the range of the sum over b in H^{(1)} ≡ Σ_b (S₁ − bp^r S₂) is implicit. | outcome not recorded. Current text: H^{(j)} is defined with the sum over b < n. | `proofs/A364175-A364178.md` Lemma B |

Not listed as rows: the cleared items of section (2); U4 (the attribution to Jacobsthal's method was not traced to a page).

### `REREVIEW-A370092--fact-only-agent.txt`

Note: `proofs/A370092.md`. Verdict: no mathematical error; two defects (E1, E2).

| Finding | Outcome | Evidence |
|---|---|---|
| E1 (§3, after Lemma B): the parenthetical "the minimum over n of v₂(b_k) − m is independent of m: 2, 4, 2, 3, …" is false over the lemma's range n ≥ m+2 (k = 4: 3, not 4; dependence on m at k = 8, 12); the committed data used only n ∈ [40, 200], m ∈ {5, 8}. | fixed in §3 (the parenthetical states the range of the committed file and the minima over the full range, citing the re-review outputs). | `numerics/out/rereview_a370092_profile_k4.txt`; `numerics/out/rereview_a370092_lemmaB.txt` |
| E2 (§6): the cited output `numerics/out/a370092_periodicity.txt` did not exist. | fixed: the file was regenerated; §6 says so. | `numerics/out/a370092_periodicity.txt` |
| U3 (references): Lengyel is cited as FPSAC 2009; the local PDF header reads "FPSAC 2008 / DMTCS proc. (subm.)". | outcome not recorded. Current text: unchanged. | `proofs/A370092.md` references |
| C2 (§6): the script list omits `lemmaB_k15_residue_check.py`, although §3 cites it. | outcome not recorded. Current text: §6 lists it. | `numerics/out/lemmaB_k15_residue_check.txt` |
| X1 (Theorem, §4): the start max α + 1 is one more than needed for odd k; §4 writes max(α_i + 1, α + 1) after saying that Proposition 1 gives α_i. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_a370092_periods.txt` |
| X2 (proof of Lemma B): "Since n ≥ m+2, f lies in the unit ball": n ≥ m+1 suffices, and (2) is stated for n ≥ m+1. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_a370092_amice.txt` |
| X3 ((P2)): the bound holds for all k ≥ 1, so "k ≥ 16" is conservative; the "≥ 2" version holds from k = 7. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_a370092_identities.txt` |
| C1, X4 (§5): "preperiod ≈ α" should read α + 1 (α for α = 7, 11); Lemma B's slack is 0 also at k = 5, 6, 7, 15 (termwise slack including g_k is 0 at k = 3 only). | outcome not recorded. Current text: §5 gives the preperiod as α + 1 for α ∈ {2, …, 6, 8, 9, 10, 12} and α for α ∈ {7, 11}; the slack sentence is unchanged. | `numerics/out/rereview_a370092_pow2_deep.txt` |
| X5 (§3, k = 3 by hand): at n = m+2 one has v₂(b₃) ≥ m+3; the stated "≥ m+2" is weaker. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_a370092_lemmaB.txt` |

Not listed as rows: the cleared items of section (2); U1 (Colmez's Théorème I.4.7 taken as published; the Lean proof of A370092 does not use it, `verification/lean-checks/A370092/README.md`); U2 (the Lemma B range m ≤ 10, k ≤ 70, n ≤ 260 was re-verified only in part; it is supported by the committed file); U4 (journal details of Schreyer and Colmez are not in the local copies).

### `REREVIEW-TheoremF-and-TheoremF-p3--fact-only-agent.txt`

Verdict: both proofs correct; four remark-level misstatements (E1–E4), one miscount and several citations without a backing file.

**Note 1: `proofs/TheoremF-p-ge-5.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| E1, X2 (§6 bullet 1): the description of the p = 3 note omits the class a ≡ b ≡ 0 (mod 3), where the valuation is ≥ 3r + 1, not 3r − 1. | fixed in §6 (the three classes are listed; the class a ≡ b ≡ 0 is described with observed valuation ≥ 3r + 1). | `numerics/out/rereview_theoremF_p3_lemmas.txt` |
| E2, C1 (§0, sharpness): "for A352373 at p = 3 the valuation is 3r − 1" is true for n = 1, 4, 7 and false for n = 2, 5, 8; the cited file does not contain the A352373 data. | fixed in §0 (the sentence is restricted to n ≡ 1 (mod 3), with ≥ 3r for n ≡ 2 (mod 3)). Current text: cites `theoremF_p3_sweep.txt` and `rereview_theoremF_p3_lemmas.txt`. | `numerics/out/theoremF_p3_sweep.txt`; `numerics/out/rereview_theoremF_p3_lemmas.txt` |
| U1 (status line): "an independent referee … re-tested them, including a term-by-term check at r = 3 (p = 5)" has no script or output. | fixed: the reference to the earlier reviewer was removed; the status line cites `rereview_theoremF_p5_valuations.py` for the term-by-term check. | `numerics/out/rereview_theoremF_p5_valuations.txt` |
| C2 (§5(a)): "independent series computation for n ≤ 15" has no artifact. | outcome not recorded. Current text: cites `rereview_theoremF_p5_identities.py` for c ≤ 5, n ≤ 25. | `numerics/out/rereview_theoremF_p5_identities.txt` |
| C3 (§5(c)): "direct symbolic simplification (sympy)" has no artifact. | outcome not recorded. Current text: §5(c) names no script; §7 lists `rereview_theoremF_p5_identities.py` as checking the §5 identities with sympy. | `numerics/out/rereview_theoremF_p5_identities.txt` |
| C4 (§5(d)): "verified for 1 ≤ n ≤ 40" (A002003) has no artifact. | outcome not recorded. Current text: "verified against the OEIS b-file for 1 ≤ n ≤ 45 in `rereview_theoremF_oeis_extra.py`". | `numerics/out/rereview_theoremF_oeis_extra.txt` |
| C5 (§7): "independent series-based recomputation of A333561 and A352373 (sympy)" has no artifact. | outcome not recorded. Current text: the sentence is absent; §7 lists the re-review scripts. | `proofs/TheoremF-p-ge-5.md` §7 |
| X1 (§4): the parenthetical saying that the weakened bounds are expected, but not shown, to give 3^{3r−1} is out of date (Theorem F₃(i) proves it). | outcome not recorded. Current text: the parenthetical states that the weakened bounds give 3^{3r−1}, which is Theorem F₃(i). | `proofs/TheoremF-p-eq-3.md` Proposition I |
| X3: `theoremF_framing_tests.py` labels (2,−2,1) as "2*A103885", while the note uses (1,−1,2). | outcome not recorded. | `numerics/scripts/theoremF_framing_tests.py` |

Not listed as rows: the cleared items of section (2); U2 (OEIS conjecture wordings checked against the web pages, not `statements/STATEMENTS.md`); U3 (external citations import nothing).

**Note 2: `proofs/TheoremF-p-eq-3.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| E3 (Remark 1): "the digit is nonzero … for A352373 at every tested (r, m)" is false; the digit is 0 at m = 2, 5, 8. | fixed in Remark 1 (nonzero exactly at m ≡ 1 (mod 3), zero at m ≡ 2 (mod 3)). | `numerics/out/rereview_theoremF_p3_lemmas.txt` |
| E4 (Remark 1, Remark 4 (V3)): "for a ≡ b ≡ 0 every constant works because both sides vanish" is false for 3 ∤ c, where only K₀ = 0 works. | fixed in Remarks 1 and 4 (both sides vanish with K₀ = 0; every constant works only if moreover 3 ∣ c). | `numerics/out/rereview_theoremF_p3_lemmas.txt`; `numerics/out/theoremF_p3_proof_checks.txt` (V3) |
| C6 (Remark 4): "17 + 11 + 9 good triples": the tag count in the cited output is 18. | fixed in Remark 4 (18 + 11 + 9). | `numerics/out/referee_theoremF_p3.txt` |
| X4 (title): "(and A333564, A119259, A333561, A333562)" reads as if all five carried p ≥ 3 conjectures; only A333565 does. | outcome not recorded. Current text: unchanged. | `statements/STATEMENTS.md` |
| X5 (Remark 3): one sweep survivor is named; there are four, all first failing at m = 5. | outcome not recorded. Current text: Remark 3 names the four. | `numerics/out/rereview_theoremF_p3_lemmas.txt` |
| X6 (Remark 4): "slack exactly 0 in the two main classes" passes over degenerate triples with A(N) − A(M) = 0. | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_theoremF_p3_lemmas.txt` |

Not listed as rows: the cleared items of section (2); U5 (the provenance of the status line's statements about earlier corrections was not checked; the content was re-verified); U6 (Beukers–Vlasenko imports nothing).

### `REREVIEW-A363983-and-A376462-first--fact-only-agent.txt`

Verdict for both notes: correct; 426 checks, 0 failures.

**Note 1: `proofs/A363983.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| C1 (§0): "(The computer checks were also run with p ∣ m.)" has no backing file. | fixed in §0 (now cites `rereview_oss_a363983.py` and `rereview_oss_a363983_wider.py`, m ∈ {p, 2p}, and states that the original scripts used only p ∤ m). | `numerics/out/rereview_oss_a363983.txt`; `numerics/out/rereview_oss_a363983_wider.txt` |
| C2 (§0 numerics): the cited sweep lacks (p, r, m) = (13, 2, 3). | outcome not recorded. Current text: unchanged. | `numerics/out/rereview_oss_a363983_wider.txt` (case covered, slack 0) |
| C3 (§4, Lemma 2): the cited script checks only the lower half sums; the upper half at p = 5 has slack 1. | outcome not recorded. Current text: §4 names the lower-half check in `a363983_oss_steps.py` and the upper-half check in `rereview_oss_lemmas.py` (slack 1 at p = 5). | `numerics/out/rereview_oss_lemmas.txt` |
| X1 (Lemma 6): "For the last, incomplete block … every block … is complete" contradicts itself. | outcome not recorded. Current text: "There is no incomplete block: …". | `proofs/A363983.md` Lemma 6 |
| X2 (Lemma 1): the note uses a stronger per-case modulus than OSS Lemma 2.1 (for Q₂); one sentence saying so would help. | outcome not recorded. | `numerics/out/rereview_oss_a363983.txt` (Q₁, Q₂, Q₃ moduli) |

Not listed as rows: the cleared items of section (2); section (3) reports no unverified concern.

**Note 2: `proofs/A376462-first-congruence.md`**

| Finding | Outcome | Evidence |
|---|---|---|
| C4 (§0): "two further exact forms (checked for n ≤ 12)": the script runs n ≤ 11. | fixed in §0 (n ≤ 11 in `a376462_representations.py`, n ≤ 13 in `rereview_oss_a376462.py`). | `numerics/out/a376462_representations.txt`; `numerics/out/rereview_oss_a376462.txt` |
| C5 (§0 and status line): "the computer checks were also run with p ∣ m" has no backing file (r = 3 and p ≤ 13 are backed). | fixed in the status line and §0 (p ∣ m cited to `rereview_oss_a376462.py`; r = 3 and p ≤ 13 to the deep direct tests). | `numerics/out/rereview_oss_a376462.txt`; `numerics/out/a376462_deep_direct_test.txt` |
| C6 (§5): "checked exactly for N ≤ 20": the script runs N ≤ 13. | fixed in §5 (N ≤ 13 in `a376462_second_structure.py`, N ≤ 20 in `rereview_oss_a376462.py`). | `numerics/out/a376462_second_structure.txt`; `numerics/out/rereview_oss_a376462.txt` |
| C7 (§5): "the referee additionally verified … p ≤ 23, m ≤ 6, including p ∣ m" has no matching file. | fixed: the reference to the earlier reviewer was removed; §5 cites `rereview_oss_a376462.py` for these ranges. | `numerics/out/rereview_oss_a376462.txt` |
| C8 (Remark): "all 120 determinants were computed and factored": the script has no factoring step; "homogenise … checked for n ≤ 4" has no script. | outcome not recorded. Current text: "all 120 distinct determinants were computed (…; no factoring step)"; the n ≤ 4 sentence is unchanged. | `numerics/out/a376462_straub_shape_search.txt` |
| X1 (§4): "min 0 attained, so the argument is tight" holds only for the I-chain and Σ_r; S_K ≡ Σ₁, the K-chain and Lemma 7 for Ψ₁ have slack ≥ 1. | outcome not recorded. Current text: §4 states which steps have slack 0 and which have slack ≥ 1. | `numerics/out/rereview_oss_a376462.txt` |
| X2 (§5): §5 is labelled "proved for r = 1" in two places while the header calls it superseded. | outcome not recorded. Current text: the §5 heading reads "proved for r = 1 (superseded: …)". | `proofs/A376462-first-congruence.md` §5 |

Not listed as rows: the cleared items of section (2); U1 (literature-context sentences not re-derived; none is used in the proof).

### `REREVIEW-A376462-shifted--fact-only-agent.txt`

Note: `proofs/A376462-shifted-congruence.md`. Verdict: correct as far as exhaustive numerical reproduction and a line-by-line audit can establish; one wrong justification sentence (E1), one citation error (C1).

| Finding | Outcome | Evidence |
|---|---|---|
| E1 (§5): "the kernel Ξ being symmetric in its two indices" is false (14,988 of 15,758 tested pairs are asymmetric); the congruence actually used is true. | fixed in §5 (the sentence now says that Ξ is not symmetric, that Lemma 3.2 treats the two indices symmetrically through its cells, and that the displayed congruence was tested exactly). | `numerics/out/rereview_shifted_misc.txt`; `numerics/out/rereview_shifted_towers.txt` |
| U2 (§9): "the first-congruence note's referee checked p ≤ 23, m ≤ 6 at r = 1" was not checkable. | fixed: the reference to the earlier reviewer was removed; §9 cites `rereview_oss_a376462.txt` for r = 1, p ≤ 23, m ≤ 6. | `numerics/out/rereview_oss_a376462.txt` |
| C1 (§9 bullet 1): the cited files contain neither p = 13 nor (5,3,1). | fixed in §9 (p = 13 and (5,3,1) cited to the files that contain them). | `numerics/out/a376462_beukers_architecture.txt`; `numerics/out/referee_B_wider_primes.txt`; `numerics/out/rereview_shifted_classSB.txt` |
| C2 (§7 Step 2): item (3) of `a376462_final_lemma_checks.txt` prints P1–P3 without defining them, so it does not show T_S ≡ 3T₁ + T₂ on its face. | outcome not recorded. Current text: the citation is unchanged. | `numerics/out/a376462_final_lemma_checks.txt`; `numerics/out/rereview_shifted_classSB.txt` (T_S − 3T₁ − T₂, slack 0) |
| X1 (§8.2): the n^k display is called "his (10)"; in Beukers, (10) is the k!·C(n,k) form. | fixed in §8.2 (the display is described as the unnumbered display before his (10), with (10) failing likewise). | `numerics/out/rereview_shifted_literature.txt` |
| X2 (§8.3): Beukers' printed proof of Lemma 4(ii) treats only the block i = 0; the general block is new in Lemma 2.6. | fixed in §8.3. | `numerics/out/rereview_shifted_literature.txt` |
| X3 (§4, (4.b.2)): "using Lemma 3.5 for the scaled j and Lemma 3.3 for the unscaled j" appears twice in one sentence. | fixed in §4. | `proofs/A376462-shifted-congruence.md` §4 |
| X4 (§7 Step 3): "reduction errors are O(p^{r−σ})" should be O(p^{r−σ+1}). | fixed in §7 Step 3. | `proofs/A376462-shifted-congruence.md` §7 |
| X5 (Lemma 3.1): the remark should say that only the top level may be restricted to units. | fixed in the remark after Lemma 3.1. | `proofs/A376462-shifted-congruence.md` §3 |

Not listed as rows: the cleared items of section (2), among them the sign of ρ′ in §5, which an earlier reviewer had reported as wrong (see the next section): the re-review found the current ρ′ exact (integrality test in 5,416 cases); U1 (Lemmas 3.1 and 3.2 checked by hand, only their applications tested); U3 (convergent series tested by truncation).

## Review round of 2026-10-15 without archived reports

Before the reports above, the notes were reviewed once more on 2026-10-15 by independent automated reviewers whose reports were not archived; this repository holds only the scripts and outputs that some of them wrote. The recorded findings and outcomes:

| Note | Finding (as recorded) | Outcome | Evidence |
|---|---|---|---|
| `proofs/A361711.md` | rigour gap at the telescoping boundary of the Zeilberger certificate | fixed (the boundary is handled through a polynomial identity, §1) | `numerics/out/rereview_short_A361711.txt` |
| `proofs/A370092.md` | start index for moduli 2·(odd) | fixed (§4 and the α = 1 clause of Proposition 2) | `numerics/out/rereview_a370092_periods.txt` |
| `proofs/A386548.md` | p ∤ n needed without loss of generality | fixed (§3, R := v_p(N)) | `numerics/out/rereview_quad_A386548_congruences.txt` |
| `proofs/A352275-u_m-family.md` | the case r + 2k = 0 of the coefficient formula | fixed (§1, "whenever r + 2k ≠ 0") | `numerics/out/rereview_short_A352275.txt` |
| `proofs/TheoremF-p-ge-5.md` | the p = 3 remark and attributions | fixed (p = 3 remark weakened, attributions corrected) | `proofs/TheoremF-p-ge-5.md` §6 |
| `proofs/A364175-A364178.md` | attributions | fixed (Lemma A attributed to Jacobsthal's classical method; the integrality of A364178 at even n attributed to the Vasyunin–Bober ratio, A295470) | `proofs/A364175-A364178.md` header |
| `proofs/A363983.md` | side remark on the signed family A = 2, B = 0 | fixed (§5: the signed case A = 2, B = 0 fails, v₅(f(5) − f(1)) = 2) | `numerics/out/rereview_oss_a363983.txt` (§5 remarks) |
| `proofs/A376462-first-congruence.md` | coverage gap for k = 0 or i = 0 in the scaled class; cosmetic items | fixed. The reviewer's extended checks (r = 3, p ≤ 13, p ∣ m) were not archived; the citation was later replaced (see C5, C7 above) | `numerics/out/rereview_oss_a376462.txt` |
| `proofs/A376462-first-congruence.md` §5 | a spurious "negation rule" derivation; missing definitions of B̃, B̃₀; boundary remarks | fixed (sentence removed, definitions and remarks added). The reviewer's observation a(3m−1) ≡ a(m−1) (mod 27) for m ≤ 20 is recorded as unproved | `numerics/out/a376462_second_r1_steps.txt` |
| `proofs/TheoremF-p-eq-3.md` | the class a ≡ b ≡ 0 (mod 3) is proved by the same argument for every c but was not stated, and three remarks misdescribed it; item (iii) of the theorem was supported only by numerics | fixed (the class is part of Theorem F₃(ii); item (iii) became the Observation) | `numerics/out/referee_theoremF_p3.txt` (0 failing checks) |
| `proofs/A376462-shifted-congruence.md` §§1–3 | Lemma 2.5: off-by-one reflection index for s = 0, and a remainder bound p^{t+t′} too weak when t < s (the lemma itself true); cosmetic items (Lemma 2.1 case v = 1, Lemma 3.4(d) parametrisation, cell notation) | fixed (proof rewritten with a separate s = 0 branch; cosmetic items corrected) | `numerics/out/referee_A_shifted_lemmas.txt` (782 checks, 0 failures) |
| `proofs/A376462-shifted-congruence.md` §§4–7 | the class-J coefficient ρ′ with its two single-index signs swapped (each piece vanishes separately); garbled modulus in §7 Step 4; wording of (4.a); no explicit statement that r = 1 and p ∣ m are covered | fixed (ρ′ corrected and the dissection script re-run; the other items corrected). The later re-review found the current ρ′ exact | `numerics/out/referee_B_shifted_assembly.txt` (357 checks, 0 failures); `numerics/out/rereview_shifted_exact.txt` |

## Later machine checks

On 2026-10-16 all twelve entries were proved in Lean 4 + Mathlib: A333561, A333562, A333565 (all p ≥ 3), A352275 (every u_m), A352373, A361711, A363983, A364175, A364178, A370092, A376462 (both congruences) and A386548. Each final theorem has the benchmark statement verbatim, depends only on the axioms propext, Classical.choice and Quot.sound, and was accepted by the benchmark's checker Comparator with the Lean kernel and the independent kernel nanoda (`lean/README.md`; `verification/lean-checks/*/README.md`; `verification/lean-checks/PROTOCOL.md`). For the statements formalised there, this supersedes the correctness questions raised in the reports above; that each Lean statement is Bala's conjecture rests on reading the definitions (`verification/STATEMENT-SHEETS.md`). In three places the Lean proofs take a different route from the notes: Lemma B of A370092 is proved with finite sums instead of Amice's theorem (`verification/lean-checks/A370092/README.md`), the A363983 proof does not assume p ∤ m (`verification/lean-checks/A363983/README.md`), and A333565 = 2·A119259 − (−1)^n is proved by Pascal's rule instead of Lagrange inversion (`verification/lean-checks/A333565/README.md`). Not covered by the Lean proofs (`lean/README.md`, `verification/lean-checks/*/README.md`, `verification/VERIFY.md` §1): Theorem F₃ beyond (a, b, c) = (2, −1, 1), that is, part (i) for general (a, b, c), the other classes of part (ii), and A333561, A333562 at p = 3 (the Lean proof at p = 3 is for A333565 only); Theorem U and the integrality of the family A364172–A364184, including A364172 and A364179 (`proofs/A364172-A364179-integrality.md`); the by-products and the sharpness claims, for example the congruences of `proofs/A361711.md` §4 and the optimality of φ(k) in `proofs/A370092.md` §5; and the identification of the benchmark's convolution formula for A333565 with Bala's generating function (1 + 4x)/((1 + x)√(1 − 8x)), which rests on the identity 2^m·C(2m, m) = [x^m](1 − 8x)^(−1/2) and is checked only on data (`verification/STATEMENT-SHEETS.md`, A333565).
