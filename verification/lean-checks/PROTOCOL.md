# Protocol for the machine checks

Every entry in this folder was checked with the procedure below. A result is recorded as machine-checked only when every gate passes; a failed gate stops the entry, the cause is fixed, and all gates are run again. Each gate's command, exit code and output file are listed in the entry's `README.md`.

## What must be trusted, and how each point is addressed

1. **The Lean statement says what the conjecture says.** Addressed by gate A (a Python mirror of the Lean definition compared with the OEIS data), gate E (the final theorem takes its type from the unmodified target file, and the module of origin of every constant in that type is listed), gate F (the benchmark's checker compares the statement with the official challenge file) and a reading by people (`verification/STATEMENT-SHEETS.md`). Only the last of these can tell whether the target file itself states Bala's conjecture faithfully.
2. **No hidden assumption** (`sorry`, a new axiom, `native_decide`, `#exit`, a disabled kernel check). Addressed by `#print axioms` run from a separate audit file, which must print exactly the line for the exact theorem name and only a subset of `propext`, `Classical.choice`, `Quot.sound`; by a scan of the build log for `sorry` and errors; and by the axiom check of the benchmark's checker.
3. **No tampering with the environment** (new notation, elaborators, instances, `run_cmd`, environment edits). Addressed by a word-boundary scan of every added or staged module for `sorry admit axiom native_decide ofReduceBool implemented_by extern unsafe skipKernelTC macro elab syntax notation instance set_option run_cmd run_elab run_meta #eval #exit initialize "import Lean" modifyEnv addDecl opaque csimp attribute scoped local private`. Every hit is reviewed and listed with a reason in `GREP-ALLOW.txt`; an unlisted hit fails the gate. The benchmark's checker never loads our compiled files.
4. **The Lean kernel.** `lean4checker` replays the compiled modules with Lean's kernel (it trusts imported `.olean` files, so it is a replay, not an independent check). The benchmark's checker Comparator re-checks the full closure of the statement with its own kernel build, and additionally with the independent kernel nanoda.

Imported lemmas need no separate trust: a lemma that compiles without `sorry` and with the standard axioms is true as stated.

## Gates

- **A. Data.** The target definition is mirrored exactly in Python (same rounding, same `toNat`, same rational arithmetic) and compared with the OEIS b-file. Zero mismatches.
- **B. Numerics.** Every lemma of the planned proof is tested numerically before it is proved. Zero failures.
- **C, D. Build in the benchmark environment** (Lean v4.27.0, Formal Conjectures `auto_oeis` commit 67338a1, in a separate workspace whose package directory is used read-only): exit 0, no error and no `sorry` in the log; `#print axioms` from a separate audit file; keyword scan with `GREP-ALLOW.txt`; `lean4checker` on every new module.
- **E. Origin.** The final theorem is stated as `type_of% @<target theorem>` in a module that imports the unmodified target module; the type is printed with `pp.explicit`, and the module of origin of every constant in it is listed.
- **F. Benchmark checker.** Comparator (leanprover/comparator 19e111e, lean4export cacf989, landrun 811cfff, as pinned in the benchmark's Dockerfile; nanoda_lib f67473b), with the official challenge file of `epoch-research/LeanOpenProblems` used byte-identical and the permitted axioms `propext`, `Classical.choice`, `Quot.sound`. Run with both kernels.
- **Controls.** For A352275, the gates were run on four files that must be rejected (a proof by `sorry`, a new `axiom`, `native_decide`, `#exit` before the final theorem); all four were rejected, and nanoda rejected an export in which one proof had been swapped for another. For every one of the twelve entries, a true but weaker statement (smaller modulus) was run through Comparator and rejected with "Challenge and solution theorem statement do not match". For Lean v4.35.0, `leanchecker` rejected a module containing a false theorem whose kernel check had been skipped (`checker-controls/`).
- **G. Repository version** (Lean v4.35.0, Mathlib as pinned in `lean/lake-manifest.json`): the definitions and the statement are copied verbatim from the target file into `lean/BalaProofs`; build exit 0; `#print axioms`; `lake env leanchecker`; a build from a fresh clone of the repository.
- **H. Lemma map.** A table from each Lean lemma to the corresponding step of the written proof (in each entry's `README.md`).
- **I. Records.** README, outputs and scripts committed; one-line commit messages.

## Rules

- One Lean job at a time, under a memory limit.
- The benchmark files and the Formal Conjectures checkout are never edited; `lake update` is never run.
- Downloaded material is used only from the pinned repositories.

## Running the scripts

The scripts in `*/scripts/` record how each check was run. They take every location outside the repository from environment variables (the original runs used fixed paths on the authors' machine; replacing them by these variables is the only change made to the scripts afterwards):

| Variable | Meaning |
|---|---|
| `BALA_CHECK_DIR` | folder holding `fc-ws/` (the Formal Conjectures workspace, Lean v4.27.0), `cmp-ws/` (the Comparator workspace) and `tools/` (builds of Comparator, lean4export, landrun and nanoda) |
| `BALA_WORK_LEAN` | the `BalaProofs` source folder of a Lean v4.35.0 project with Mathlib built (the generators write the repository versions there) |
| `LOP_ISOLATED` | `apn/data/oeis/Isolated` in a checkout of `epoch-research/LeanOpenProblems` (the official challenge files) |
| `LEAN4CHECKER` | the `lean4checker` binary for Lean v4.27.0 (default: `lean4checker` on the `PATH`) |

Paths inside the repository are found from the script's own location.

## Rebuilding the two workspaces

1. Export Formal Conjectures at commit 67338a157bbb8d87e9a349d662f82a868bda6327 twice, as `fc-ws/` and `cmp-ws/`, and fetch its dependencies as pinned in its `lake-manifest.json`.
2. Run `./assemble-workspaces.sh <folder>`. It collects the Lean sources of all entry folders: `BalaCheck/` goes into `fc-ws/`, and `Submission/`, `run/` and `challenges/` go into `cmp-ws/`. Files shared by several entries must be identical, except `GREP-ALLOW.txt`, whose final version is the union of the per-entry versions. On 2026-10-16 the 231 assembled files were compared with the workspaces in which the checks were run (the challenge files with `epoch-research/LeanOpenProblems` at commit 3d11d0979a58170ad868c95a63673ab7b29ace5d): all identical, and every `BalaCheck.*` and `Submission.*` import resolves.
3. Append to `fc-ws/lakefile.toml` a library `BalaCheck` with `globs = ["BalaCheck.+"]`, and to `cmp-ws/lakefile.toml` the libraries `Challenge` (`srcDir = "run"`) and `Submission`, as in the benchmark's Dockerfile.
4. Before each Comparator run, copy the entry's official challenge file from `challenges/` to `cmp-ws/run/Challenge.lean`, then run `scripts/run-comparator.sh run/<config>.json <absolute output path>`.
