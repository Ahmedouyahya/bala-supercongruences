# Literature and tools for Target 1 (collected 2026-10-15)

## Foundations (supercongruences)
- Wolstenholme (1862); Morley (1895) half-index congruence; Carlitz (1953) mod p⁴ refinement; Glaisher.
- Jacobsthal (1949/1952), Kazandzidis (1968): C(np^k, mp^k) ≡ C(np^(k−1), mp^(k−1)) (mod p^(3k)), p ≥ 5. Survey: Meštrović, "Wolstenholme's theorem: its generalizations and extensions (1862–2012)", arXiv:1111.3057. Lucas-type survey: arXiv:1409.3820.
- Granville (1997), "Arithmetic properties of binomial coefficients I: binomial coefficients modulo prime powers".
- Cai (2002): Morley for composite moduli. Cai–Granville: arXiv math/0603488. Hessami Pilehrood–Tauraso: Morley mod p⁶ (search their TAMS/other papers on multiple harmonic sums).
- Apéry (1979); Chowla–Cowles–Cowles (1980); Gessel (1982); Beukers (1985, 1987); Coster (1988, thesis): A(mp^r) ≡ A(mp^(r−1)) mod p^(3r); Ahlgren–Ono (2000).
- Zagier (2009) sporadic sequences. Osburn–Sahu (2009/2011) arXiv:0906.3413; Osburn–Sahu–Straub (2013) arXiv:1312.2195 "Supercongruences for sporadic sequences"; Straub (2014) arXiv:1401.0854 "Multivariate Apéry numbers and supercongruences of rational functions"; Gorodetsky (2021) arXiv:2102.11839; Straub (2023) arXiv:2301.12248 "Gessel–Lucas congruences for sporadic sequences".
- Beukers–Vlasenko, "Dwork crystals I–III" (III: arXiv:2105.14841); Vlasenko ICTP notes arXiv:2412.13313; Beukers (2024/25) "Supercongruences using modular forms" arXiv:2403.03301.
- Multiple harmonic sums: Hoffman arXiv math/0401319; Zhao; Tauraso; Meštrović.

## Family-specific
- F1: Adamczewski, "OEIS Open" arXiv:2608.11941 (Appendix A summary of the A333096 proof); Epoch results repo `epoch-research/LeanOpenProblems-results` (no licence file; a local clone was used).
- F5: Kallat, "A Proof of Bala's Congruence Conjectures for A158690", arXiv:2609.07238 (Lean; needs G ∈ ℤ[[y]]); Schreyer, "Rigged Horse Numbers and their Modular Periodicity", J. Integer Seq. 28 (2025) 25.4.1 (Fubini numbers mod K, max period λ(K)); Asgari–Jahangiri, J. Integer Seq. 21 (2018) (r-Fubini mod any s, incl. powers of 2); Touchard/Bell periodicity literature (Lunnon–Pleasants–Stephens 1979).
- F4: Morley/Carlitz/Cai/Granville above; Bober (2009) factorial ratios arXiv:0709.1977; Soundararajan (2019) integral factorial ratios; Radcliffe (2026) integrality of A364175 (link on OEIS); rbajaj5's "Bober packet" (unreviewed drafts).
- F3: Osburn–Sahu–Straub; Sun Z.-W./Z.-H. congruence papers on Apéry-like numbers (e.g. arXiv:2103.05830, 2409.06544).
- F2: Straub 2014/2023; Gorodetsky 2021; Beukers–Vlasenko III.

## Recent proofs of Bala conjectures (precedents and style guides)
- Kallat 2026 (arXiv 2609.07238); arXiv 2607.18313 (A028342); Epstein 2026 (OEIS A277060 PDF); Bala, "A congruence for A361715" (OEIS PDF, Aug 2026, harmonic sums); Wentao Li, github.com/VictorLiwentao/lean-oeis-proofs (A003161/2 in Lean); Fried, J. Integer Seq. 29 (2026) 26.1.8 (ten OEIS conjectures).

## Tools
- Lean 4 + Mathlib (elan/lake; the Mathlib cache is several GB). Comparator / SafeVerify (Epoch) for checking against benchmark targets. Tau Ceti (AI-written Lean library).
- SageMath (installed), Python sympy (installed) for numerics; PARI/GP optional.
- OEIS JSON API: https://oeis.org/search?fmt=json&q=id:A333561
