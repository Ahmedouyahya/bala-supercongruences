# Papers

The results are written up as two papers in LaTeX (`amsart`).

| Folder | Paper | Pages |
|---|---|---|
| `paperA-coefficient-towers/` | A cubic supercongruence tower for [x^{cN}]((1+x)^a(1−x)^b)^N, the prime 3, and two further conjectures of Bala (Theorem F and the prime 3, including exceptional triples; A333561, A333562, A333565, A352373, Bala's general conjectures on A352373 and A333715; A386548; A370092) | 12 |
| `paperB-apery-and-factorial-ratios/` | Cubic supercongruences for a Dixon-type sum, fractional factorial ratios and two Apéry-like sequences (A361711 for all odd n; A364172, A364175, A364178, A364179; A363983; A376462, both congruences; repairs to Beukers 1985) | 21 |

A352275 (a corollary of a machine-proved lemma of Epoch AI, with no human-readable proof) is not included in either paper.

- `common/macros.tex`: shared preamble. `common/refs.bib`: shared bibliography.
- Build a paper: `cd paperA-coefficient-towers; latexmk -pdf main.tex`.
