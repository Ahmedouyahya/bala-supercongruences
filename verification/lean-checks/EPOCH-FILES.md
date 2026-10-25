# Files from Epoch AI

Three Lean proofs produced in Epoch AI's OEIS Open evaluation are used by the machine checks. They are the work of Epoch AI. Their source repository, `epoch-research/LeanOpenProblems-results` (commit fd09021e79869476ef83cda231312f1a2a89c8d7), has no licence file; Epoch AI gave permission to use them, on the condition that the work is credited to Epoch AI. They are therefore not covered by this repository's licence (see `NOTICE`).

| Upstream file (in `runs/` of that repository) | What it proves | SHA-256 of the upstream file |
|---|---|---|
| `oeis-lite-200usd-sol-nk5wh4g0vh3546nm/oeis_333096_supercongruence_conjecture/Submission/Spec.lean` | A333096, including the scaling lemma `FNat_scale_supercongruence` | `c395ea2342f90decd0c508eb3191470a3703b67984fa61594ee12a2197477576` |
| `oeis-lite-200usd-deep-ant-ewytt1ev01pbycd6/oeis_361883_conjecture_0/Submission/Spec.lean` | A361883, including the Jacobsthal–Kazandzidis bound `JAC_bound` | `501a46f5d9b1833ed62d84f8c865f9d940a02c4ba9f2311f30bbb58b95647e84` |
| `oeis-lite-200usd-fable-i7s7n9q7v4emgjp7/general_supercongruence_conjecture/Submission/Spec.lean` | A333042 (general form), including the power-series exponential and Dwork's lemma | `395daeb47ef78e79737c18738f2c499fcd9672fa6e2e0b26c6d6b17fe9eb4a1c` |

## Where they are used, and what was changed

**Repository version (Lean v4.35.0)**, in `lean/BalaProofs/`: `EpochA333096.lean`, `EpochA361883.lean`, `EpochA333042.lean`. Each file's header lists every change from the upstream file: the import line, an enclosing namespace, and the renamings needed for Lean v4.35.0 and current Mathlib.

**Benchmark-environment checks (Lean v4.27.0)**, copied byte for byte from the workspaces in which the checks were run:

| File | Upstream | Change | SHA-256 |
|---|---|---|---|
| `A352275/comparator-workspace/Submission/EpochOrig.lean` | A333096 | none (byte-identical) | `c395ea2342f90decd0c508eb3191470a3703b67984fa61594ee12a2197477576` |
| `A352275/fc-workspace/BalaCheck/EpochSol.lean` | A333096 | line 45 `def a` renamed `def a_unused_epoch` (the target file also defines `a`) | `219f40423cc0cc0beea85d7889f6c29875a50ece0a0e61571dfefb4c936f61e2` |
| `A386548/fc-workspace/BalaCheck/EpochJac.lean`, `A386548/comparator-workspace/Submission/EpochJac.lean` (identical) | A361883 | two comment lines naming the source, and the whole file wrapped in `namespace Epoch361883` | `d2601ef78ada5f1eae4f6d7c5060b967eda90784468e755a5502264be0473c7f` |
| `TheoremF-A333561-A333562-A352373/fc-workspace/BalaCheck/EpochExp.lean`, `TheoremF-A333561-A333562-A352373/comparator-workspace/Submission/EpochExp.lean` (identical) | A333042 | a module docstring naming the source, and the whole file wrapped in `namespace Epoch333042`; the import line, line 17 upstream, is line 1 here, above the docstring (the docstring's words "the import line is kept" mean that the import itself is unchanged) | `91a082f27fbae8882b0be62f6f22b52f0445cb22b9f430d4710f82af2cdfc5bc` |

The keyword hits in these files (`private` declarations, linter options, `maxHeartbeats`) are listed with reasons in the `GREP-ALLOW.txt` of each workspace.

## Which proofs use them

- `FNat_scale_supercongruence` (A333096): A352275 (every u_m).
- `JAC_bound` (A361883): A386548, and through it A363983 and A376462.
- The power-series exponential and Dwork's lemma (A333042): Theorem F, hence A333561, A333562, A352373 and A333565.
