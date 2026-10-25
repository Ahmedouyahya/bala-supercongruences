# Machine check of A386548

Result: Bala's conjecture on A386548, in the form of the benchmark target `oeis_A386548_supercongruence_conjecture` (all primes p ≥ 5, all n, k ≥ 1, modulus p^(2k)), is proved in Lean and accepted by every check below. Checked on 2026-10-16.

## The proof

| Lean declaration (`A386548.*`) | Statement | Paper step (`proofs/A386548.md`) |
|---|---|---|
| `Bser`, `Bser_mul`, `U`, `U_key`, `subst_Bser_mul`, `series_eq` | (1 + X²/(1−X))^(−N) = (1−X²)^N (1+X³)^(−N) as power series, via substitution into the series of (1+X)^(−N) | §1, reformulation |
| `coeff_subst_U`, `coeff_rhs`, `a_eq_S` | the target's sum a(N) equals S(N) = Σ_{2j+3m=N} (−1)^(j+m) C(N,j) C(N+m−1,m) for N ≥ 1 | §1, formula (1) |
| `unscaled_nat`, `t_unscaled` | if 2j+3m = N, p^k ∣ N and p ∤ j, then p^(2k) divides the term (this includes p ∤ j ⇔ p ∤ m) | §3, synchronisation and unscaled terms |
| `factor1`, `factor2`, `scaled_int`, `t_scaled` | for scaled pairs the level-N and level-M terms agree modulo p^(2·v_p(M)+3), from `Epoch361883.JAC_bound` (Kazandzidis's congruence) | §3, scaled terms |
| `S_split`, `S_cong` | S(pM) ≡ S(M) modulo p^(2k) when p^(k−1) ∣ M | §3, conclusion |

The scaled-term bound needs no case split: `JAC_bound` with v_p C(M,j) + v_p(j) ≥ v_p(M) gives the modulus p^(2·v_p(M)+3) directly, which is at least p^(2k).

## Files

- Repository version (Lean v4.35.0): `lean/BalaProofs/A386548Defs.lean` (the target's `def a`, verbatim), `A386548Series.lean`, `A386548Padic.lean`, `A386548Main.lean`, `A386548.lean` (the target's theorem statement, verbatim), importing `lean/BalaProofs/EpochA361883.lean`: the accepted Lean proof of OEIS A361883 from the OEIS Open evaluation (run `oeis-lite-200usd-deep-ant-ewytt1ev01pbycd6`, commit fd09021e), included with permission from Epoch AI, wrapped in `namespace Epoch361883` and adapted to Lean v4.35.0 with four renamed lemmas, listed in its header.
- Benchmark-environment version (Lean v4.27.0, Formal Conjectures 67338a1): `fc-workspace/BalaCheck/`; the final theorem is `A386548_from_target : type_of% @oeis_A386548_supercongruence_conjecture`, importing the unmodified target module; Epoch's file is used unchanged inside the namespace.
- Official checker setup: `comparator-workspace/`; challenge = `apn/data/oeis/Isolated/oeis_A386548_supercongruence_conjecture.lean` of `epoch-research/LeanOpenProblems`, byte-identical.

## Checks and results

| Check | Result | Output |
|---|---|---|
| Earlier proofs: Epoch AI's runs on this target (four, all not accepted), GitHub, arXiv, the web, rbajaj5's repository | none found | `literature/PRIOR-CLAIMS.md` |
| Target definition vs OEIS b-file (32 terms) | 0 mismatches | `outputs/gateAB.out` |
| Every step tested numerically: identity (N ≤ 300), synchronisation and valuations (11,892 index pairs), final congruence (62 cases, minimal slack 0), `JAC_bound` statement (2,340 cases) | 0 failures | `outputs/gateAB.out` |
| Benchmark environment: build, `sorry` and error scan, `#print axioms` (exact names) for the final theorem, `S_cong`, `a_eq_S`, `scaled_int`, `unscaled_nat`; keyword scan of all four modules; lean4checker | build exit 0; standard axioms only; 0 keyword hits; lean4checker exit 0 on all four | `outputs/gates-real-1.txt` |
| Statement printed with `pp.explicit`; module of origin of every constant | constants from Lean core, standard Mathlib definitions and the target module (`a`) only | `outputs/origin-audit.txt` |
| Comparator against the official challenge, Lean kernel and nanoda kernel | accepted: "Your solution is okay!" | `outputs/comparator-nanoda.txt` |
| Comparator control: a true but weaker statement (modulus p^(2k−1)), proved from the real theorem | rejected: "Challenge and solution theorem statement do not match" | `outputs/comparator-neg-weak.txt` |
| Repository version (Lean v4.35.0): build of the six files, `#print axioms`, verbatim definition and statement, `leanchecker` on five modules | exit 0, no errors, standard axioms, verbatim, `leanchecker` exit 0 | `outputs/repo-v4.35-*.txt` |

The gates themselves were tested on planted faults (sorry, an added axiom, `native_decide`, `#exit`) during the A352275 check (`verification/lean-checks/A352275/outputs/negative-controls.txt`), and nanoda's type checker was shown to reject a tampered proof there.
