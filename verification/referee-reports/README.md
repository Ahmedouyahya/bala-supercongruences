# Independent review reports

The files in this folder are verbatim independent review reports of the proof notes, produced by automated reviewers (language models, named in each file) on 2026-10-15 from the notes as they stood at the time; each file's first lines record its date, provenance and input. They are kept as evidence, not as authority: the disposition of every finding (what was fixed, what was a reviewer error) is recorded in `DISPOSITIONS.md`.

Changes to the files since they were produced (2026-10-16): the absolute path of the authors' working folder is replaced by `<working folder>` wherever it occurs, and in the provenance lines at the top of each file (written by the authors, not by the reviewers) the machine is described as "the authors' machine" and the pointer to the disposition record reads `DISPOSITIONS.md`. Nothing else was changed. `PROMPT.txt` is the review instruction. The notes have since been renamed; the table gives the current file.

| File | Note concerned | Date |
|---|---|---|
| `A352275-u_m-corollary-of-A333096-machine-proof--deepseek-v4.1-flash-free.txt` | `proofs/A352275-u_m-family.md` | 2026-10-15 |
| `A361711-proof--nemotron-3-ultra-free.txt` | `proofs/A361711.md` | 2026-10-15 |
| `A363983-proof--nemotron-3-ultra-free.txt` (truncated run) | `proofs/A363983.md` | 2026-10-15 |
| `A363983-proof--nemotron-3-ultra-free--rerun.txt` | `proofs/A363983.md` | 2026-10-15 |
| `A364175-A364178-factorial-ratio-towers--nemotron-3-ultra-free.txt` | `proofs/A364175-A364178.md` | 2026-10-15 |
| `A370092-periodicity-proof--nemotron-3-ultra-free.txt` | `proofs/A370092.md` | 2026-10-15 |
| `A376462-proof-first-congruence--nemotron-3-ultra-free.txt` | `proofs/A376462-first-congruence.md` | 2026-10-15 |
| `A376462-proof-first-congruence--nemotron-3-ultra-free--with-background.txt` (second run, with the A363983 note supplied) | `proofs/A376462-first-congruence.md` | 2026-10-15 |
| `A376462-shifted-congruence-proof--nemotron-3-ultra-free.txt` | `proofs/A376462-shifted-congruence.md` | 2026-10-15 |
| `A386548-quadratic-tower-proof--nemotron-3-ultra-free.txt` | `proofs/A386548.md` | 2026-10-15 |
| `TheoremF-coefficient-framing-proof--nemotron-3-ultra-free.txt` | `proofs/TheoremF-p-ge-5.md` | 2026-10-15 |
| `TheoremF-p3-proof--nemotron-3-ultra-free.txt` | `proofs/TheoremF-p-eq-3.md` | 2026-10-15 |
| `TheoremF-p3-proof--deepseek-v4.1-flash-free.txt` | `proofs/TheoremF-p-eq-3.md` | 2026-10-15 |
| `REREVIEW-A352275-and-A361711--fact-only-agent.txt` | `proofs/A352275-u_m-family.md`, `proofs/A361711.md` | 2026-10-15 (night) |
| `REREVIEW-A386548-and-A364175-A364178--fact-only-agent.txt` | `proofs/A386548.md`, `proofs/A364175-A364178.md` | 2026-10-15 (night) |
| `REREVIEW-A370092--fact-only-agent.txt` | `proofs/A370092.md` | 2026-10-15 (night) |
| `REREVIEW-TheoremF-and-TheoremF-p3--fact-only-agent.txt` | `proofs/TheoremF-p-ge-5.md`, `proofs/TheoremF-p-eq-3.md` | 2026-10-15 (night) |
| `REREVIEW-A363983-and-A376462-first--fact-only-agent.txt` | `proofs/A363983.md`, `proofs/A376462-first-congruence.md` | 2026-10-15 (night) |
| `REREVIEW-A376462-shifted--fact-only-agent.txt` | `proofs/A376462-shifted-congruence.md` | 2026-10-15 (night) |
| `PROMPT.txt` | the review instruction used for the reports above (except the REREVIEW round, whose protocol is stated in each file's header) | 2026-10-15 |

The REREVIEW reports were produced under the rule that a mistake may be reported only after it has been reproduced by an exact test; their check scripts are `numerics/scripts/rereview_*.py` and the outputs `numerics/out/rereview_*.txt`. The reports refer to the notes by their former paths under `notes/` and to scripts under `numerics/`; the current locations are `proofs/` and `numerics/scripts/`.
