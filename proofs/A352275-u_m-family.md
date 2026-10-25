# A352275 and the whole family u_m: a corollary of the machine proof of A333096

**Status.** Proved and machine-verified in Lean 4 + Mathlib (`lean/BalaProofs/A352275.lean`, the benchmark statement verbatim; all checks, including the benchmark's checker Comparator with the Lean and nanoda kernels, in `verification/lean-checks/A352275/README.md`). The proof is a corollary of a lemma that is already machine-verified (Lean 4 + Mathlib, SafeVerify-accepted) inside the Epoch/OEIS Open proof of A333096; nothing here is new mathematics beyond one elementary identity, and the point is that the verified lemma is stronger than the theorem it was used for. Machine proof: LM agent "GPT-5.6 Sol" in T. Adamczewski's OEIS Open evaluation (arXiv:2608.11941), results repository `epoch-research/LeanOpenProblems-results`, run `oeis-lite-200usd-sol-nk5wh4g0vh3546nm`, sample `oeis_333096_supercongruence_conjecture`, file `Submission/Spec.lean` (2546 lines, no `sorry`, verdict "C", SafeVerify passed, Lean v4.27.0). Conjecture: Peter Bala (OEIS A352275, 2022). Verification: `numerics/scripts/sweep_2026-10-15.py` and `numerics/scripts/rereview_short_A352275.py` (outputs `numerics/out/sweep_2026-10-15.txt`, `numerics/out/rereview_short_A352275.txt`); review reports `verification/referee-reports/A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt` and `verification/referee-reports/REREVIEW-A352275-and-A361711--fact-only-agent.txt`.

## 1. Statement

Let c(x) = (1 − sqrt(1 − 4x))/(2x) be the Catalan generating function. For integers r and N ≥ 0 put

    T(r, N) := Σ_{k=0}^{N} [x^k] c(x)^r,      [x^k] c(x)^r = C(r+2k−1, k) − C(r+2k−1, k−1)  (generalized binomials; = 1 for k = 0; = r/(r+2k) · C(r+2k, k) whenever r + 2k ≠ 0).

Bala's sequences: A333093–A333097 are a_m(n) = T(mn, n) (the n-th order Taylor polynomial of c^{mn} at x = 1); A352275 is u_2(n) = T(n, 2n); more generally u_m(n) = T(n, mn) (so u_1 = A333093, u_2 = A352275, u_3 = A352276), with u_m(0) = 1.

**Theorem (two-parameter scaling).** Let p ≥ 5 be prime, v ≥ 0, and let N ≥ 1 and r ≥ −N be integers with p^v | N and p^v | r. Then

    T(pr, pN) ≡ T(r, N)   (mod p^{3(v+1)}).

**Corollary (Bala's conjecture for A352275 and for every u_m).** For p ≥ 5, m ≥ 1, n ≥ 1, k ≥ 1:  u_m(n p^k) ≡ u_m(n p^{k−1}) (mod p^{3k}).

Proof of the corollary from the theorem: take N = m n p^{k−1}, r = n p^{k−1}, v = k − 1; then T(pr, pN) = u_m(n p^k) and T(r, N) = u_m(n p^{k−1}). (The Formal Conjectures statement `u_m_supercongruence_conjecture` in `statements/lean-targets/352275_4b1f2230.lean` is exactly this: for n ≥ 1 the benchmark defines u m n as a sum of `(Rat.floor (n/(n+2k)·C(n+2k,k))).toNat` over k ≤ mn, and each term is a non-negative integer equal to [x^k]c(x)^n (n + 2k ≥ 1), so floor and toNat are the identity; the n = 0 branch is defined separately as 1 = T(0,0) and is never used, since the Corollary quantifies n ≥ 1, so that N = mnp^{k−1} ≥ 1 and r = np^{k−1} ≥ 1 in the application of the Theorem.)

## 2. The verified lemma

In `Spec.lean` the following are defined and proved (names and statements copied for reference; the code itself is not reproduced):

- `FNat (A B : ℕ) : ℤ := coeff_B ( Qseries * (1+X)^A )`, where `Qseries` is the integer power series with `cyclo3 * Qseries = 1 − X^2`, `cyclo3 = X^2 + X + 1` (so Qseries = (1 − X^2)/(1 + X + X^2)).
- `formalCatalanCoeff r k = Ring.choose (r+2k−1) k − Ring.choose (r+2k−1) (k−1)` (k ≥ 1), `= 1` (k = 0); `formalPartial r N = Σ_{k≤N} formalCatalanCoeff r k`.
- `formalPartial_eq_FNat (A N : ℕ) : formalPartial ((A : ℤ) − 2*(N : ℤ)) N = FNat A N`  (Spec.lean l. 1389; the subtraction is in ℤ).
- `FNat_scale_supercongruence {p lev B Y : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p^lev ∣ B) (hY : p^lev ∣ Y) : FNat (p*(B+Y)) (p*B) ≡ FNat (B+Y) B [ZMOD (p:ℤ)^(3*(lev+1))]`  (Spec.lean l. 1169).
- The A333096 result itself is obtained from it as `a_gen_nat_scale` via `a_gen_nat_eq_FNat (M N : ℕ) (hN : 0 < N) : a_gen M N = FNat ((M+2)N) N` (l. 1448, 1545), i.e. with B = N, Y = (M+1)N. (`Qseries` is defined by explicit coefficients, `PowerSeries.mk qCoeff`; `cyclo3 * Qseries = 1 − X²` is the proved lemma `cyclo3_mul_Qseries`, l. 383.)

Since formalCatalanCoeff r k = [x^k] c(x)^r for every integer r (standard), formalPartial r N = T(r, N), and the lemma reads: for A = B + Y, with p^v | B and p^v | Y,

    T(A − 2B, B) scales: T(p(A−2B), pB) = FNat(pA, pB) ≡ FNat(A, B) = T(A−2B, B)  (mod p^{3(v+1)}).

Put N = B, r = A − 2B = Y − B. The hypotheses p^v | B, p^v | Y are equivalent to p^v | N, p^v | r; the constraint Y ≥ 0 is r ≥ −N. This is the Theorem. (The restriction r ≥ −N is an artefact of the B + Y parametrisation of the Lean lemma, not of the mathematics: numerically the congruence also holds for −3N ≤ r < −N, p ∈ {5,7}, N ≤ 14 — 210 cases, 0 violations, `numerics/scripts/rereview_short_A352275.py`)

## 3. Why FNat is the truncated Catalan power (independent derivation)

With c = 1 + X and x = X/(1+X)^2 (so c = 1 + x c^2 holds identically), the change-of-variable formula for coefficient extraction ([x^k] F(x) = [X^k] F(x(X)) ψ(X)^k (1 − Xψ'(X)/ψ(X)) for x = X/ψ(X), here ψ = (1+X)^2) gives

    [x^k] c(x)^r = [X^k] (1+X)^{r+2k} (1 − X)/(1 + X) = [X^k] (1 − X)(1+X)^{r+2k−1},

which is C(r+2k−1, k) − C(r+2k−1, k−1). Summing over k ≤ N with U := X/(1+X)^2:

    T(r, N) = [X^N] (1 − X)(1+X)^{r+2N−1} Σ_{t=0}^{N} U^t = [X^N] (1 − X)(1+X)^{r+2N−1}/(1 − U)
            = [X^N] (1 − X)(1+X)^{r+2N+1}/(1 + X + X^2) = [X^N] (1 − X^2)/(1 + X + X^2) · (1+X)^{r+2N}

(the terms t > N of the geometric series do not contribute to [X^N]). This is FNat(r + 2N, N). Equivalently, with X ↦ X/(1−X) one gets Adamczewski's form β(S, N) = [X^N] (1−2X)/((1−X)(1−X+X^2)) · (1−X)^{−S}, S = r + N; the identity T(r,N) = β(r+N, N) was checked for 1 ≤ r ≤ 8, 0 ≤ N ≤ 8 (`numerics/scripts/sweep_2026-10-15.py`).

## 4. Numerical confirmation (exact arithmetic, `numerics/scripts/sweep_2026-10-15.py`, output in `numerics/out/`)

- Two-parameter statement with independent S, N (1 ≤ S ≤ 39, 1 ≤ N ≤ 24, p ∈ {5,7,11,13}): v_p(β(pS,pN) − β(S,N)) − 3(v+1) ≥ 0 always, with minimum 0 (sharp). Here β(S,N) = T(S−N, N) and v := min(v_p(N), v_p(S−N)) is the largest v with p^v | N and p^v | r = S − N, as in the Theorem's hypothesis; with v_p(N) alone in place of v the inequality would be false (e.g. p = 5, S = 11, N = 10 gives valuation 4, not ≥ 6; `numerics/scripts/rereview_short_A352275.py`).
- u_m(n p^k) − u_m(n p^{k−1}) for m ∈ {1,2,3}, p ∈ {5,7,11}, n ∈ {1,2}, k ∈ {1,2}: valuations ≥ 3k always; exactly 3k in 20 of the 36 cases.
- u_2 = A352275 agrees with Σ_{k≤2n} [x^k] c(x)^n for n ≤ 18, u_1 = A333093 for n ≤ 22, u_3 = A352276 for n ≤ 15 (`numerics/scripts/rereview_short_A352275.py`, against the OEIS data; the sweep script does not perform this check).

## 5. What is and is not established

- Established: the Corollary, machine-verified end to end: the Lean file of the A333096 proof is included as `lean/BalaProofs/EpochA333096.lean`, and `lean/BalaProofs/A352275.lean` proves the benchmark statement from it (`verification/lean-checks/A352275/README.md`).
- Not done: (a) a human-readable proof of the lemma (the proof lives in the Lean file; the run's own `metadata.json` summarises the method: Frobenius expansion (1+X)^{pA} = Σ_j p^j C(A,j) frobError^j (1+X^p)^{A−j}, antisymmetry of the error polynomial modulo X^2+X+1, valuation bounds. Adamczewski's Appendix A.1 (Table 1) describes instead the second accepted machine proof of A333096, run `oeis-lite-200usd-fable-i7s7n9q7v4emgjp7` (4057 lines, 0 sorry), whose theorem `C2` proves the two-parameter statement p^{3(1+v)} | bet(pS,pN) − bet(S,N) for every integer S with p^v | S, N, i.e. without the restriction r ≥ −N); (b) checking which other OEIS entries are rays (αn, βn) of T(r, N): all "Taylor polynomial of c(x)^{αn} of order βn" sequences with α ≥ −β are covered (this OEIS search has not been carried out yet).
- Sharpness: the modulus p^{3k} cannot be improved in general (valuation exactly 3k occurs, e.g. m = 1, p = 7, n = 1, k = 1).

## 6. Suggested OEIS comment (draft; not posted)

"The conjectured supercongruences hold. They follow from the lemma `FNat_scale_supercongruence` in the Lean 4 proof of the A333096 conjecture produced in the OEIS Open evaluation (Adamczewski, arXiv:2608.11941; results repository, run oeis-lite-200usd-sol-nk5wh4g0vh3546nm): that lemma states that S(r, N) := Sum_{k=0..N} [x^k] c(x)^r satisfies S(p r, p N) == S(r, N) (mod p^(3(v+1))) whenever p >= 5 and p^v divides both r and N (r >= −N); u_m(n) = S(n, m n). — <name>, <date>."

## References
- P. Bala, OEIS A352275 (2022); A333093–A333097 (2020).
- T. Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?, arXiv:2608.11941 (2026), Appendix A.
- epoch-research/LeanOpenProblems-results, run oeis-lite-200usd-sol-nk5wh4g0vh3546nm, `Submission/Spec.lean` (no licence file; reused with permission from Epoch AI and included, adapted to Lean v4.35.0, as `lean/BalaProofs/EpochA333096.lean`).
- R. Meštrović, Wolstenholme's theorem: its generalizations and extensions, arXiv:1111.3057 (for the Jacobsthal–Kazandzidis background cited on A352275).
