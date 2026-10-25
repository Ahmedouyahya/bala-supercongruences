# VERIFY.md — how to check this work yourself

Written 2026-10-15; updated 2026-10-16 after all twelve entries were machine-checked. Everything here runs from the repository root with `python3 -I <script>`;
the archived outputs are in `numerics/out/`, and `numerics/README.md` says where each script writes
(some write next to themselves, some print to standard output).
Nothing in this file is a proof; it tells you what evidence exists for each claim and how to reproduce it.

## 0. The honest picture in one paragraph

Every statement (Bala's conjectures on all twelve OEIS entries plus the by-products) has been tested numerically with exact
big-integer arithmetic far beyond the range any human referee would try, and the exponents are *sharp*
(the observed p-adic valuation equals the claimed one in many cases), so the statements are almost certainly
true. The *proofs* were checked by independent review reports (§4), which found real errors in first drafts,
all fixed; such reviews can still share blind spots. A machine-checked proof (Lean, §5) needs no trust in any reader: all twelve benchmark statements are proved in Lean, each accepted by the benchmark's checker with two independent kernels. What remains open to human judgement is whether each Lean statement says what Bala conjectured (`verification/STATEMENT-SHEETS.md`), and the written proofs of the results that are not formalised (listed in §5). For a human reader, the short notes
(§1 items 1–4) are checkable in an afternoon; the long ones (Theorem F, Theorem F₃, A363983, A376462) need a
specialist and a day each.

## 1. Four levels of evidence, and which items have which

| Level | What it establishes | What it cannot establish |
|---|---|---|
| L1 theorem-level numerics | the *statement* holds for all tested (p, r, m) | that it holds for all p, r, m |
| L2 proof-level numerics | every lemma and every intermediate quantity of the *written proof* has the claimed valuation, recomputed from the note's own definitions by an independent script | that the logical glue between the lemmas is right |
| L3 independent review | an independent reader found no error (or found errors, now fixed) | more than the reader's competence |

In the L3 column, "reports" counts the report files in `verification/referee-reports/` for the note (all produced by language models).
| L4 machine check (Lean) | the proof is correct, full stop | nothing — but it covers only what has been formalised |

| Item | Note | L1 | L2 | L3 | L4 |
|---|---|---|---|---|---|
| A352275 | `proofs/A352275-u_m-family.md` | yes | n/a (corollary) | 2 reports | yes: `lean/BalaProofs/A352275.lean` (benchmark statement verbatim; standard axioms; also accepted by the benchmark's checker Comparator with the Lean and nanoda kernels, `verification/lean-checks/A352275/`) |
| A361711 | `proofs/A361711.md` | p ≤ 43, k ≤ 4 | Zeilberger certificate checked symbolically (sympy) | 2 reports | **yes: `lean/BalaProofs/A361711.lean` compiles sorry-free, standard axioms only, exact benchmark statement** |
| A386548 | `proofs/A386548.md` | yes | yes | 2 reports | yes: `lean/BalaProofs/A386548.lean` (benchmark statement verbatim; standard axioms; also accepted by the benchmark's checker Comparator with the Lean and nanoda kernels, `verification/lean-checks/A386548/`) |
| A370092 | `proofs/A370092.md` | yes (incl. 2-powers) | yes (`lemmaB_*`) | 2 reports | yes: `verification/lean-checks/A370092/` (with an elementary proof of the 2-adic lemma in place of Amice's theorem; the sharpness of φ(k) is not formalised) |
| A333561/2/5, A352373 (Theorem F, p ≥ 5) | `proofs/TheoremF-p-ge-5.md` | p ≤ 13, r ≤ 3, wide (a,b,c) sweep | yes (`theoremF_framing_tests.py`) | 2 reports | yes: Theorem F for all a, b, c (`TF.theoremF`) and the benchmark statements of A333561, A333562, A352373 (`verification/lean-checks/TheoremF-A333561-A333562-A352373/`) and A333565 (`verification/lean-checks/A333565/`) |
| A333565 etc. at p = 3 (Theorem F₃) | `proofs/TheoremF-p-eq-3.md` | r ≤ 7 | yes (288 + an independent 0-fail run) | 3 reports | for (a,b,c) = (2,−1,1) only, which gives A333565 at p = 3 (`verification/lean-checks/A333565/`); A333561 and A333562 at p = 3: no |
| A364175, A364178 | `proofs/A364175-A364178.md` | yes | yes | 2 reports | **yes: `lean/BalaProofs/A364175.lean`, `lean/BalaProofs/A364178.lean` compile sorry-free, standard axioms only, exact benchmark statements (incl. the integrality of A364178)** |
| A363983 | `proofs/A363983.md` | yes | yes (`a363983_oss_steps.py`) | 3 reports (two runs of one reviewer, one truncated) | yes: `verification/lean-checks/A363983/` (including the non-negativity required by the target's `Int.toNat`) |
| A376462 first congruence | `proofs/A376462-first-congruence.md` | p ≤ 31, r ≤ 5 | yes | 3 reports | yes: `verification/lean-checks/A376462/` (both congruences) |
| A376462 shifted congruence | `proofs/A376462-shifted-congruence.md` | p ≤ 31, r ≤ 5 | yes: 782 + 357 checks, re-run at (7,3,1), (5,3,2), (5,4,1), (11,2,1), (13,2,1), (7,2,2) | 2 reports, and 2 earlier reviews that were not archived | yes: `verification/lean-checks/A376462/` |

The complete list of archived review reports, with the note each one concerns, is in
`verification/referee-reports/README.md`; the disposition of every finding is in `verification/referee-reports/DISPOSITIONS.md`. Not machine-checked: Theorem F₃ beyond (2,−1,1), Theorem U and the integrality of the family A364172–A364184 (`proofs/A364172-A364179-integrality.md`), the by-products and the sharpness claims, and the identification of A333565's convolution formula with Bala's generating function.

## 2. Theorem-level checks you can run (L1) — these need no understanding of the proofs

Each script computes the sequence straight from its OEIS definition and prints the p-adic valuation of
a(N) − a(N/p) next to the required exponent. "OK" on every line is a pass; the number after `v=` is the
observed valuation, and when it equals the required one the claim is sharp (cannot be improved).

- A376462, both congruences, deep: `numerics/scripts/a376462_deep_direct_test.py` (≈ 3 min) and
  `numerics/scripts/a376462_deep_direct_test2.py` (r up to 5, ≈ 30–60 min). Output `numerics/out/a376462_deep_direct_test*.txt`.
- Theorem F (p ≥ 5) and Theorem F₃ (p = 3) for the whole 3-parameter family:
  `numerics/scripts/theoremF_deep_direct_sweep.py` (seconds) and `..._sweep2.py` (minutes). A pass is `FAILURES: 0`;
  the "worst slack" numbers show how tight the exponents are (0 = sharp).
- The remaining items: `numerics/scripts/sweep_2026-10-15.py` (all the conjectured statements at modest depth),
  `numerics/scripts/a361711_valuations.py`, `numerics/scripts/a370092_periodicity.py`, `numerics/scripts/fractional_factorial_sweep.py`.

If any of these ever prints FAIL, the corresponding *statement* is false and the proof is wrong somewhere.

## 3. Proof-level checks (L2) — each lemma and each step of the written proofs

These scripts do not reuse the project's helper code; they were written independently from the notes' definitions.

- A376462 shifted proof, lemma bank (§§1–3 of the note): `numerics/scripts/referee_A_shifted_lemmas.py`.
- A376462 shifted proof, assembly (§§4–7): `numerics/scripts/referee_B_shifted_assembly.py`;
  deeper and wider: `numerics/scripts/referee_B_deeper_cases.py`, `numerics/scripts/referee_B_wider_primes.py`.
  A pass is `No structural failures` and no line containing FAIL. Each line reports the *slack* of a piece
  (observed valuation minus the valuation the proof consumes); slack 0 means the inequality used in the proof is
  tight there, which is also why these scripts have real power: a one-unit mistake in any claimed modulus
  would appear as a negative slack.
- Theorem F₃: `numerics/scripts/theoremF_p3_proof_checks.py` and the independent `numerics/scripts/referee_theoremF_p3.py`.
- Theorem F (p ≥ 5): `numerics/scripts/theoremF_framing_tests.py`.
- A361711 closed form (the only computer-algebra step in the project): `numerics/scripts/a361711_zeilberger_check.py`
  checks the rational-function form of the Zeilberger certificate symbolically (sympy `cancel`), and the identity with the factorial form of the certificate at all integer points 0 ≤ k ≤ n + 2, 2 ≤ n < 40, with its boundary terms; `numerics/scripts/rereview_short_A361711.py` re-parses the certificate independently (its T3).
- A370092, 2-adic lemma: `numerics/scripts/lemmaB_finite_checks.py`, `numerics/scripts/lemmaB_stirling_2adic.py`, `numerics/scripts/lemmaB_k15_residue_check.py`.
- Independent re-check scripts (2026-10-15 night), one family per note group, written from the notes' own definitions under the rule that no error may be reported without a reproducing test: `numerics/scripts/rereview_short_*.py` (A352275, A361711), `rereview_quad_*.py` (A386548, A364175/8), `rereview_a370092_*.py`, `rereview_theoremF_*.py`, `rereview_oss_*.py` (A363983, A376462 first), `rereview_shifted_*.py`. Each prints PASS/FAIL per check; the expected result is 0 FAIL except the lines that reproduce the already-corrected remark errors listed in `verification/referee-reports/DISPOSITIONS.md`.

## 4. Independent review reports (L3)

- The disposition of every finding of every round is recorded in `verification/referee-reports/DISPOSITIONS.md`.
- Independent review reports, stored verbatim (except the path substitution stated in that folder's README) in `verification/referee-reports/`: at least one per note
  (`<note>--nemotron-3-ultra-free.txt` for nine notes, `A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt` for A352275)
  and a second one for Theorem F₃ (`TheoremF-p3-proof--deepseek-v4.1-flash-free.txt`); A363983 and the first A376462 congruence have two runs each. Read the VERDICT line and
  the listed issues. `DISPOSITIONS.md` lists all 121 findings with the outcome recorded for each; for 57 of them no outcome was recorded at the time, and the file then describes the current text of the note at that place. The review instruction is `verification/referee-reports/PROMPT.txt`.
- Re-review reports of the night round, one per note group, with their own check scripts (the `rereview_*.py` of §3):
  `REREVIEW-A352275-and-A361711--fact-only-agent.txt`, `REREVIEW-A386548-and-A364175-A364178--fact-only-agent.txt`,
  `REREVIEW-A370092--fact-only-agent.txt`, `REREVIEW-TheoremF-and-TheoremF-p3--fact-only-agent.txt`,
  `REREVIEW-A363983-and-A376462-first--fact-only-agent.txt`, `REREVIEW-A376462-shifted--fact-only-agent.txt`.

## 5. Machine check (L4)

`lean/` is a Lean 4 + Mathlib project: `cd lean && lake exe cache get && lake build` compiles every module ("Build completed successfully" with no `sorry` warning is a pass); `lean/README.md` lists the final theorem of each entry and its supporting modules. All twelve benchmark statements are proved: A333561, A333562, A333565 (all p ≥ 3), A352275 (every u_m), A352373, A361711, A363983, A364175, A364178, A370092, A376462 (both congruences) and A386548. In addition, Bala's two general conjectures on A352373 and A333715 are proved for p ≥ 5 (`verification/lean-checks/BalaGeneral/`; no benchmark statement exists for them, so their statements were written from Bala's text and checked by Comparator against a challenge file written the same way).

How each was checked is in `verification/lean-checks/PROTOCOL.md` and in the README of each entry folder there: a build in the benchmark's own environment (Lean v4.27.0, Formal Conjectures), `#print axioms`, a keyword scan, `lean4checker`, an audit of the origin of every constant in the statement, the benchmark's checker Comparator against the official challenge file with Lean's kernel and the independent kernel nanoda, controls that must be rejected (among them a true but weaker statement for every entry), and a rebuild of the repository version (Lean v4.35.0) from a fresh clone. `verification/lean-statement-check/` checks independently, in Lean and as text, that the repository's definitions and statements are the benchmark's.

What a passing check means, and what it does not: a theorem that compiles with no `sorry` and whose `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` is proved exactly as stated. Whether the statement is the intended conjecture is a separate check by reading (`verification/STATEMENT-SHEETS.md`, one sheet per entry). Lean's conventions matter in that reading: natural-number subtraction stops at 0, division by 0 gives 0, and `Int.toNat` maps negative numbers to 0 (the targets for A363983 and A333565 use it, and their Lean proofs prove the needed non-negativity).

Epoch's proof of A333096 (`lean/BalaProofs/EpochA333096.lean`, see `lean/README.md`) was replayed on 2026-10-16 in both environments: original file in Lean v4.27.0 (exit 0, `lean4checker` exit 0, statement identical to the target) and adapted file in Lean v4.35.0 (exit 0, standard axioms only).

## 6. How to hand a note to a friend

Give them the note, the matching L1 script and the matching L2 script. Ask three questions only:
(1) is every lemma stated with all its hypotheses, (2) at every use of a lemma, are those hypotheses met,
(3) at every "≡ (mod p^e)" step, where does the exponent e come from. Those three questions found every
error the reviews found so far.

## 7. Results of the verification round of 2026-10-15 (evening)

All outputs are in `numerics/out/` and `verification/referee-reports/`; every number below can be regenerated with the commands in §2–§4.

**Theorem-level (L1), straight from the OEIS definitions.**
- A376462, both congruences (`a376462_deep_direct_test.txt`, `..._test2.txt`): every case passes. New depths: r = 2 up to p = 31; r = 3 at p = 5 (m = 2, 3), 7 (m = 1, 2), 11, 13; r = 4 at p = 5 and p = 7; r = 5 at p = 5 (N = 3125, both valuations exactly 15). The observed valuation equals the required 3r in most cases (sharp), so the statements cannot be strengthened and the tests have no slack to hide behind.
- Theorem F and Theorem F₃ (`theoremF_deep_direct_sweep.txt`, `..._sweep2.txt`): 0 failures over a, b ∈ [−5, 7], c ≤ 4 at p = 3 (r ≤ 5) and a, b ∈ [−4, 6], c ≤ 3 at p = 3 (r ≤ 7), p = 5 (r ≤ 4), p = 7 (r ≤ 3), p = 11 (r ≤ 3), p = 13 (r ≤ 2). Worst slack is 0 in every class at every prime: the p = 3 classification is exact.

**Proof-level (L2), the shifted A376462 proof replayed from the note's definitions.**
- `referee_B_wider_primes.txt`: (11,2,1), (13,2,1), (7,2,2) — no structural failure, no FAIL line; 99 of 131 measured pieces have slack exactly 0.
- `referee_B_deeper_cases.txt`: (7,3,1), (5,3,2) and (5,4,1) — the last one exercises three genuine induction steps of §4/§5 and the strata of §7 at σ up to 3; no structural failure, no FAIL line; again 99 pieces with slack 0.

**Independent review reports (L3).** At least one report exists for each of the ten notes (two runs for A363983 and for the first A376462 congruence) (`<note>--nemotron-3-ultra-free.txt` for nine of them, `A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt` for A352275) and a second one for Theorem F₃ (`TheoremF-p3-proof--deepseek-v4.1-flash-free.txt`). Verdicts and what was done with them:
- A376462 shifted congruence — CORRECT (`A376462-shifted-congruence-proof--nemotron-3-ultra-free.txt`, 75 KB, every section recomputed; its three "least sure" steps are Lemma 2.5's general block, the tight X_s step of §4, and the σ-strata of §7 — exactly the places where the L2 replays show slack 0 and pass up to r = 4).
- Theorem F₃ — CORRECT in both reports (the second re-derived every lemma with its own sympy code). Two presentational remarks (imports from the p ≥ 5 note; the order in which g_t ∈ ℤ_(3) is established) were incorporated.
- Theorem F (p ≥ 5) — CORRECT WITH FIXES: the c = 0 case was unaddressed (trivial; sentence added) and a harmless sign remark on Lemma 4 (added).
- A370092 — CORRECT WITH FIXES: the report objected that Amice's theorem needs continuous functions; the functions in question are analytic on each class mod 2, hence in LA₁ and continuous (classes are open). The note now says so explicitly, and the finite check for k = 15 is now a self-contained script (`lemmaB_k15_residue_check.py`, 0 violations).
- A363983 — CORRECT WITH FIXES: "p ∤ m" was used but not stated (now stated with the reduction), and the regrouping in Lemma 6 is now written out.
- A376462 first congruence — CORRECT WITH FIXES: same p ∤ m remark (added); the §5 expansions are now referenced to Lemma 1.3 of the shifted note, which proves them for all r (§5 is superseded).
- A361711 — CORRECT WITH FIXES: three expository items (inversion step of Lemma 3, nonvanishing of a(M′), integrality of e_j), all added.
- A386548 — CORRECT WITH FIXES: the report called two identities false; both were re-derived and are correct (C(N+k−1,k) = (N/k)C(N+k−1,k−1), and C(D−1,k′) = C(M+k′−1,k′)); one-line verifications were added to forestall the misreading.
- A364175/A364178 — CORRECT WITH FIXES: the only "gap" is a lemma imported from the Theorem F note (present in the project, not supplied with the note under review); one exposition item on the floor-function bookkeeping was clarified.
- A352275 — CORRECT WITH FIXES (`A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt`): no error; two expository items fixed, see `verification/referee-reports/DISPOSITIONS.md`.

The outcome recorded for each finding, or the absence of a record, is in `verification/referee-reports/DISPOSITIONS.md`.

**Machine check (L4).** See §5: since 2026-10-16 all twelve benchmark statements are machine-checked (`verification/lean-checks/`).
