# Machine check of two general conjectures of Peter Bala (p ≥ 5)

Result: two general conjectures that Bala states in comments on OEIS entries are proved in Lean for all primes p ≥ 5, as corollaries of Theorem F (`TF.theoremF`). Checked on 2026-10-16.

1. **OEIS A352373** (revision 24), comments: "let r and s be integers and define a sequence (a(r,s;n))n>=1 by a(r,s;n) = [x^n] ( (1 + x)^r * (1 - x)^s )^n. Conjecture: for each r and s the above supercongruences hold for the sequence a(r,s;n) for n >= 1", the supercongruences being "a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) ... for all primes p >= 5 and positive integers n and k". Lean: `BalaGeneral.bala_A352373_general`, for all integers r, s.
2. **OEIS A333715** (revision 35), comment: "The same congruences may hold more generally for the sequences a(r,s,n) := [x^(r*n)]( (1 + x)/(1 - x) )^(s*n), r a positive integer and s an integer", the congruences being a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for primes p >= 5 and positive integers n and k. Bala's PDF "A supercongruence for A002003" (2020, linked from A002003) states the same conjecture as its eq. (12). Lean: `BalaGeneral.bala_A333715_general`, for every r ≥ 0 and every integer s.

There is no benchmark statement for these conjectures. The Lean statements were written from Bala's text; `verification/STATEMENT-SHEETS.md` puts them next to it for a human reader.

## Definitions

For an integer t, (1 + x)^t is Mathlib's `PowerSeries.binomialSeries ℤ t`, the power series with coefficients `Ring.choose t k` (the generalized binomial coefficient t(t−1)⋯(t−k+1)/k!), and (1 − x)^t is obtained from it by x ↦ −x (`PowerSeries.rescale (-1)`):

- `aRS r s n = coeff n ((binomialSeries ℤ r * rescale (-1) (binomialSeries ℤ s)) ^ n)`, that is [x^n]((1 + x)^r (1 − x)^s)^n;
- `aRSn r s n = coeff (r * n) ((binomialSeries ℤ s * rescale (-1) (binomialSeries ℤ (-s))) ^ n)`, that is [x^(rn)]((1 + x)^s (1 − x)^(−s))^n = [x^(rn)]((1 + x)/(1 − x))^(sn).

## The proof

- `expS_zsmul_lp`, `expS_zsmul_lm`: exp(t·log(1+x)) = (1+x)^t and exp(t·log(1−x)) = (1−x)^t for every integer t (for t ≥ 0 from Epoch AI's `expS_nsmul` and `TF.expS_lp`, `TF.expS_lm`; for t < 0 by uniqueness of inverses, since (1+x)^t (1+x)^(−t) = 1 by Mathlib's `binomialSeries_add`).
- `coeffPow_eq_A`: [x^(cN)]((1+x)^a (1−x)^b)^N equals `TF.A a b c N`, the coefficient for which Theorem F is proved; this holds for all integers a, b and all c, N ≥ 0.
- `tower_int'`: Theorem F as a divisibility statement for an integer-valued sequence (the same proof as `TF.tower_int`, which is for ℕ-valued sequences).
- The two theorems are Theorem F with (a, b, c) = (r, s, 1) and (s, −s, r).
- `BalaGeneralCheck.lean`: `aRS (-1) (-3) n` equals the benchmark's own definition of A352373 for every n ≥ 1, a check that the general definition specializes correctly.

## Checks and results

| Check | Result | Output |
|---|---|---|
| Python mirror of `aRS` and `aRSn` (generalized binomial coefficients, truncated power series) against the OEIS data of every sequence Bala names: A000984, A001700 (offset 1), A002003, A091527, A119259, A156894, A165817, A234839, A348410, A351857, A352373 for a(r,s;n), and A333715, A002003, A103885 for a(r,s,n) | 0 mismatches (n ≤ 15, resp. n ≤ 12) | `outputs/gateAB_general.out` |
| The congruences tested numerically, −4 ≤ r, s ≤ 4, p ∈ {5, 7, 11}, k ≤ 2 at p = 5; and a(r,s,n) for 1 ≤ r ≤ 3, −3 ≤ s ≤ 3, p ∈ {5, 7} | 1,056 tests, 0 failures, minimal slack 0 | same |
| Benchmark environment (Lean v4.27.0, Formal Conjectures 67338a1): build, `sorry`/error scan, `#print axioms` by exact name, keyword scan with `GREP-ALLOW.txt`, `lean4checker` on the module and every Theorem F module it imports | all PASS, verdict ACCEPT; axioms `propext`, `Classical.choice`, `Quot.sound` | `outputs/gates-v427.txt` |
| Comparator (same versions as for the twelve entries) with a challenge file written from Bala's text (`comparator-workspace/challenges/Challenge-BalaGeneral.lean`), Lean kernel and nanoda | accepted: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" | `outputs/comparator-nanoda.txt` |
| Control: the first theorem with the weaker modulus p^(3k−1) | rejected: "Challenge and solution theorem statement do not match" | `outputs/comparator-neg-weak.txt` |
| Control: the challenge with `rescale (1)` in place of `rescale (-1)` in the definition of `aRS` | rejected: "Const does not match between challenge and target 'BalaGeneral.aRS'" | `outputs/comparator-neg-def.txt` |
| Repository version (Lean v4.35.0): build, `#print axioms`, `lake env leanchecker` | exit 0; standard axioms for both theorems and for `aRS_neg_one_neg_three_eq_A352373`; leanchecker exit 0 on both modules | `outputs/repo-v4.35.txt` |

## Scope and credit

- The case r = 1 or s = 1 of the first conjecture (c = a or c = b in Theorem F) follows from Straub, Algebra & Number Theory 8 (2014), Theorem 3.2(b), and the case r = 0 or s = 0 is a single binomial coefficient (Jacobsthal–Kazandzidis). Likewise, the cases r = s and r = −s of the second conjecture are covered by Straub.
- Theorem F uses Epoch AI's power-series exponential and Dwork's lemma (`verification/lean-checks/EPOCH-FILES.md`).
- The identification of the sequences Bala names (for example A091527, A119259, A348410, A351857) with a(r,s;n) is not formalised here, apart from A352373; for A348410 and A351857 it is immediate from their definitions as numbers of solutions, and for A091527 and A119259 it is a formula line on the entry.
