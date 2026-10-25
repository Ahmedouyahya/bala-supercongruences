# Beukers (1985): the two printed-argument issues, checked against the printed paper

Checked 2026-10-19. Source: F. Beukers, *Some congruences for the Apéry numbers*, J. Number Theory 21 (1985) 141–155. The file used is the publisher's scan (PDF title "PII: 0022-314X(85)90047-2", Acrobat Capture 2003), fetched from https://sites.math.rutgers.edu/~zeilberg/Combo20/projects/beukers85.pdf. Pages 148, 149, 153 and 154 were read from page images, not from an OCR layer. The PDF is not redistributed here.

This records the check of the Beukers display against the printed paper. All three statements made in `proofs/A376462-shifted-congruence.md` §8 are confirmed.

## 1. Lemma 4(i): the reduction on p. 149 is false (the lemma itself is true)

Printed (p. 149, after "Since Σ′1/κ ≡ 0 (mod p^{2s}), Σ′1/κ² ≡ 0 (mod p^s), etc., we see that it suffices to show"):

  Σ_{n=0}^{p^t−1} n^k Σ′_{λ=1}^{n} 1/λ ≡ 0 (mod p^t)  ∀ k ∈ ℤ_{≥0},

"or, equivalently," (10): Σ_{n=0}^{p^t−1} k!·C(n,k)·(Σ′_{λ≤n} 1/λ) ≡ 0 (mod p^t).

This is false. Exact computation (valuation of the left side, required t):

| p | t | k = 0 | k = 1 | k = 2 | required |
|---|---|---|---|---|---|
| 5 | 1 | 0 | 0 | 0 | 1 |
| 5 | 2 | 1 | 1 | 1 | 2 |
| 7 | 1 | 0 | 0 | 0 | 1 |
| 7 | 2 | 1 | 1 | 1 | 2 |
| 11 | 1 | 0 | 0 | 0 | 1 |
| 11 | 2 | 1 | 1 | 1 | 2 |

For example, p = 5, t = 1, k = 0: Σ_{n<5} H′_n = 0 + 1 + 3/2 + 11/6 + 25/12 = 77/12 ≡ 1 (mod 5). In general Σ_{n<p^t} H′_n = p^t H′_{p^t−1} − (p^t − p^{t−1}) ≡ p^{t−1} (mod p^t).

*Where it goes wrong.* The next display writes the sum by Abel summation, with correction term Σ_{n=0}^{p^t−1} (k!/(n+1))·C(n+1,k+1). That uses Σ′_{λ≤n+1} 1/λ − Σ′_{λ≤n} 1/λ = 1/(n+1) for every n. This is true only when p ∤ n+1; the restriction is dropped.

*Status of Lemma 4(i).* The lemma is true (proved by a different route as Lemma 2.5 of our note, and checked numerically). Only its printed proof is defective.

## 2. Lemma 4(ii): stated too weakly, proved only for the first block

Printed (p. 148): (ii) Σ′_{[kp^{−t}]=i} (1/k) Σ′_{λ=1}^{kp^s} 1/λ ≡ 0 (mod p^{t+s}) ∀ i ∈ ℤ.

The printed proof (p. 149) sums over k = 1, …, p^t − 1 only, that is the block i = 0. The statement is for every block i.

## 3. The final step (pp. 153–154) needs the stronger form

On p. 154 Beukers applies Lemma 3(ii) with a_k = (p^{−s}/k)·Σ′_{λ≤kp^s} 1/λ (p ∤ k) and the kernel at level r − s, and checks the block hypothesis "according to Lemma 4(ii)". The count:

- Lemma 3(ii) at level r − s gives Σ a_k·(kernel) ≡ 0 (mod p^{r−s});
- so Σ′(1/k)(Σ′_{λ≤kp^s} 1/λ)·(kernel) = p^s Σ a_k·(kernel) ≡ 0 (mod p^r), which is what is written ("zero mod p^r, as required");
- with the prefactor m p^{r−s} this makes the term (13) ≡ 0 only modulo p^{2r−s}. The proof needs p^{2r} ("We must show that each of the terms (13) is zero mod p^{2r}", p. 153).

So the printed argument is short by p^s for every stratum 1 ≤ s ≤ r − 1, and is complete only for r = 1. The repair: normalise by p^{−2s} instead (a_k stays integral, since Σ′_{λ≤kp^s} 1/λ ≡ 0 mod p^{2s} by his Lemma 1). The block hypothesis then needs Lemma 4(ii) modulo p^{t+2s}, on every block. That is Lemma 2.6 of `proofs/A376462-shifted-congruence.md`. The count becomes (r−s) + 2s + (r−s) = 2r.

## 4. Consequence

Beukers' Theorem 1 (the shifted congruences for the ζ(2) and ζ(3) Apéry numbers) is true. Its statement is also implied by later work (Coster 1988; Straub 2014 via negative indices). The printed proof has the two repairable gaps above. They can be stated in the paper as "the printed argument needs the following repair", with page references, without claiming the theorem was wrong.
