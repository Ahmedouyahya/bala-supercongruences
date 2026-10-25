# A376462: proof of the shifted supercongruence a(mp^r − 1) ≡ a(mp^{r−1} − 1) (mod p^{3r}) for all r ≥ 1 (p ≥ 5)

**Status.** Machine-checked in Lean 4 + Mathlib together with the first congruence (the benchmark statement; `verification/lean-checks/A376462/README.md`, which lists where the Lean proof departs from this note). Proved (elementary): Beukers' 1985 architecture for the ζ(2) Apéry numbers, extended to the two-index sum. Method credit: F. Beukers, *Some congruences for the Apéry numbers*, J. Number Theory 21 (1985) 141–155 (Lemmas 1–5 there; see §8 for two places where his printed arguments need repair, both repaired below), A. Straub 2014 (Lemma 5.6, the abstract form of the block induction), Osburn–Sahu–Straub 2016; the first congruence and the case r = 1 of the second are proved in `proofs/A376462-first-congruence.md`, and this note proves the second for all r. Conjecture: Peter Bala (OEIS A376462, 2024; the entry states both congruences a(np^r) ≡ a(np^{r−1}) and a(np^r − 1) ≡ a(np^{r−1} − 1) (mod p^{3r}) for primes p ≥ 5). Verification: every lemma and every intermediate congruence was first measured numerically (scripts listed in §9); independent check scripts `numerics/scripts/referee_A_shifted_lemmas.py` (§§1–3, 782 checks, 0 failures), `referee_B_shifted_assembly.py` (§§4–7, 357 checks, 0 failures), `referee_B_deeper_cases.py`, `referee_B_wider_primes.py`, `rereview_shifted_*.py`, `a376462_deep_direct_test.py` and `a376462_deep_direct_test2.py` (outputs in `numerics/out/`); review reports `verification/referee-reports/A376462-shifted-congruence-proof--nemotron-3-ultra-free.txt` and `verification/referee-reports/REREVIEW-A376462-shifted--fact-only-agent.txt`.

## 0. Statement, conventions, reduction

**Theorem.** Let p ≥ 5 be prime, m ≥ 1, r ≥ 1, N := mp^r, M := mp^{r−1}. Then a(N − 1) ≡ a(M − 1) (mod p^{3r}), where
 a(n) = Σ_{k,j≥0} C(n,k)² C(n+k,k) C(n,k+j)² C(n+j,j)   (A376462; identity with Bala's definition proved in the first-congruence note, §5).

Conventions. For a ∈ ℤ and b ∈ ℤ: C(a,b) := a(a−1)⋯(a−b+1)/b! for b ≥ 0 and C(a,b) := 0 for b < 0 (so C(a,b) ∈ ℤ; for a ≥ 0 it is the usual binomial, zero for b > a). Two identities used throughout: C(a,b) = (a/b)·C(a−1,b−1) for b ≥ 1, and C(n+b−1,b) = (−1)^b C(−n,b) for b ≥ 0. ℤ_p = p-adic integers, v = v_p. Σ′ and Π′ restrict an index to values prime to p. For t ≥ 0 and l ≥ 0 the block B_t(l) := {k ∈ ℤ_{≥0} : [k/p^t] = l} (so B_0(l) = {l}). H′_n := Σ′_{λ≤n} 1/λ (H′_0 = 0). For t ≥ 0: σ_t(n) := Σ′_{k∈B_t(n)} 1/k (note σ_0(n) = 1/n if p ∤ n, 0 if p | n, and Σ_{n∈B_u(l)} σ_t(n) = σ_{t+u}(l)). S_d(x) := Σ′_{μ≤x} μ^{−d}. Throughout, "integral" means "in ℤ_p".

Terms. With the convention above, for N ≥ 1 and k, j ≥ 0,
 S̃(N;k,j) := C(N−1,k)² C(N+k−1,k) C(N−1,k+j)² C(N+j−1,j),   a(N−1) = Σ_{k,j≥0} S̃(N;k,j)
(the terms vanish unless k + j ≤ N − 1; this is the re-indexing of the first-congruence note, §5).

Reduction. It suffices to treat p ∤ m: if p | m, the claim for (m, r) is implied by the claim for (m/p, r+1), which is modulo p^{3r+3}. Nothing below actually needs p ∤ m, but it keeps the block pictures simple.

Four classes. Split the index set by (p | k ?, p | j ?): S (both divisible), K (p ∤ k, p | j), J (p | k, p ∤ j), B (neither divisible), and write a(N−1) = Σ_S + Σ_K + Σ_J + Σ_B. The theorem follows from
 (S) Σ_S ≡ a(M−1), (K) Σ_K ≡ 0, (J) Σ_J ≡ 0, (B) Σ_B ≡ 0, all modulo p^{3r},
proved in §§4–7 after the lemma bank of §§1–3.

## 1. Exact product identities and the basic congruences (any m ∈ ℤ)

**Lemma 1.1 (Beukers, Lemma 2; exact).** Let m ∈ ℤ, s ≥ 1, L := mp^s, L′ := mp^{s−1}, n ≥ 0.
 (i) C(L−1, n) = C(L′−1, [n/p]) · Π′_{λ≤n} (L−λ)/λ = (−1)^{n−[n/p]} C(L′−1,[n/p]) · Π′_{λ≤n} (1 − L/λ).
 (ii) If p | n: C(L, n) = C(L′, n/p) · Π′_{λ≤n} (L−λ)/λ = C(L′, n/p) · Π′_{λ≤n} (1 − L/λ).
Proof. (i) In C(L−1,n) = Π_{λ=1}^{n} (L−λ)/λ split the factors with p | λ, λ = pμ: Π_{μ≤[n/p]} (L′−μ)/μ = C(L′−1,[n/p]); the number of λ ≤ n prime to p is n − [n/p]. (ii) C(L,n) = (L/n)C(L−1,n−1) = (L′/(n/p))·C(L′−1,n/p−1)·Π′_{λ≤n−1}(L−λ)/λ by (i) with [ (n−1)/p ] = n/p − 1, and Π′_{λ≤n−1} = Π′_{λ≤n} since p | n; the number of such λ is n − n/p, even for p odd. ∎
Negative m is allowed, which gives the identities for C(−L−1, n) and C(−L, n).

**Lemma 1.2 (congruences; Beukers' (ii), (iii)).** For m ∈ ℤ, s ≥ 1, n ≥ 0:
 (a) (−1)^n C(mp^s−1, n) ≡ (−1)^{[n/p]} C(mp^{s−1}−1, [n/p])  (mod p^s);
 (b) C(mp^s, pn) ≡ C(mp^{s−1}, n)  (mod p^s).
Proof. In ℤ[[X]], (1−X)^p = 1 − X^p + pW with W ∈ ℤ[X], so (1−X)^{mp^s} = (1−X^p)^{mp^{s−1}}·(1 + pW/(1−X^p))^{mp^{s−1}} ≡ (1−X^p)^{mp^{s−1}} (mod p^s) (expand the last factor binomially: v(C(mp^{s−1},i)p^i) ≥ s−1−v(i)+i ≥ s). Comparing coefficients of X^{pn} gives (b). Dividing by 1 − X = (1−X^p)/(1+X+…+X^{p−1}) gives (1−X)^{mp^s−1} ≡ (1−X^p)^{mp^{s−1}−1}(1+X+…+X^{p−1}) (mod p^s), whose coefficient of X^n is (−1)^{[n/p]}C(mp^{s−1}−1,[n/p]); the left side has coefficient (−1)^nC(mp^s−1,n). ∎
Consequences used below: C(mp^s−1,n)² ≡ C(mp^{s−1}−1,[n/p])² (mod p^s); for p ∤ n, [(n−1)/p] = [n/p], so (−1)^{n−1}C(mp^s−1, n−1) ≡ (−1)^{[n/p]}C(mp^{s−1}−1,[n/p]) (mod p^s).

**Lemma 1.3 (first-order expansion).** Let L ∈ pℤ_p and, for x ≥ 0, P_x := Π′_{λ≤x}(1 − L/λ), P̄_x := Π′_{λ≤x}(1 + L/λ). Let E := Π_{i} P_{x_i}^{a_i} P̄_{y_i}^{b_i} be a finite product with a_i, b_i ∈ ℤ_{≥0}. Expanding, E = Σ_{d≥0} L^d e_d with e_0 = 1,
 e_1 = −Σ_i a_i H′_{x_i} + Σ_i b_i H′_{y_i},   e_2 = ½ e_1² − ½ Σ_i ( a_i S_2(x_i) + b_i S_2(y_i) ),
and every e_d lies in ℤ_p. In particular E ≡ 1 + L e_1 (mod L²ℤ_p) and v(e_2) ≥ min(2v(e_1), min_i v(S_2(x_i)), min_i v(S_2(y_i))).
Proof. Group the factors by λ: the factor belonging to λ is (1 − y)^{α_λ}(1 + y)^{β_λ} with y = L/λ and α_λ, β_λ ∈ ℤ_{≥0}, whose expansion is 1 + c_λ y + d_λ y² + … with c_λ = β_λ − α_λ, d_λ = C(α_λ,2) + C(β_λ,2) − α_λβ_λ, and all coefficients in ℤ. Hence e_d is a ℤ-combination of products of d factors 1/λ (λ prime to p), so e_d ∈ ℤ_p; e_1 = Σ_λ c_λ/λ is the stated expression; and e_2 = Σ_{λ<μ} c_λc_μ/(λμ) + Σ_λ d_λ/λ² = ½ e_1² + Σ_λ (d_λ − ½c_λ²)/λ² with d_λ − ½c_λ² = −½(α_λ + β_λ), which is the stated formula (α_λ + β_λ counts, with multiplicity, the products P_{x_i}, P̄_{y_i} whose range contains λ). ∎

## 2. Harmonic block lemmas

**Lemma 2.1 (power sums over full blocks).** Let v ≥ 1, d ≥ 1, and let e(d) := 0 if (p−1) ∤ d, e(d) := 1 + v_p(d) if (p−1) | d. Then Σ_{u∈(ℤ/p^v)^×} u^{−d} ≡ 0 (mod p^{v−e(d)}) (read as "no condition" if v ≤ e(d)). Consequently, for y ≥ 1 and x = p^v y: S_d(x) = Σ′_{μ≤x} μ^{−d} ≡ 0 (mod p^{v−e(d)}), and for d = 2: S_2(x) ≡ 0 (mod p^v), and Σ′_{μ∈B_v(l)} μ^{−2} ≡ 0 (mod p^v) for every block.
Proof. (ℤ/p^v)^× is cyclic; let g generate it. Multiplying the summation variable by g permutes the group, so (g^{−d} − 1)·Σ ≡ 0 (mod p^v). If (p−1) ∤ d then g^{−d} ≢ 1 (mod p) and the factor is a unit. If (p−1) | d there is nothing to prove for v = 1 (e(d) ≥ 1); for v ≥ 2 write d = (p−1)d′; g^{p−1} = 1 + pz with p ∤ z (g generates (ℤ/p²)^×), and v_p(g^{−d}−1) = v_p((1+pz)^{−d′} − 1) = 1 + v_p(d′) = e(d) (lifting the exponent; p odd). For S_d(x): μ ↦ μ mod p^v maps the units of each block B_v(l) bijectively onto (ℤ/p^v)^× and μ^{−d} ≡ (μ mod p^v)^{−d} (mod p^v); x = p^v y consists of y full blocks. The case d = 2: p ≥ 5 gives (p−1) ∤ 2. ∎

**Lemma 2.2 (block Wolstenholme; Beukers, Lemma 1).** For t ≥ 0 and l ≥ 0: σ_t(l) = Σ′_{k∈B_t(l)} 1/k ≡ 0 (mod p^{2t}). Hence H′_{x} ≡ 0 (mod p^{2v}) whenever p^v | x.
Proof. t = 0 is empty. For t ≥ 1 the map k ↦ (2l+1)p^t − k is an involution of the units in B_t(l) without fixed points, and 1/k + 1/((2l+1)p^t−k) = (2l+1)p^t/(k((2l+1)p^t − k)) ≡ −(2l+1)p^t k^{−2} (mod p^{2t}), so 2σ_t(l) ≡ −(2l+1)p^t Σ′_{k∈B_t(l)} k^{−2} ≡ 0 (mod p^{2t}) by Lemma 2.1. H′_{p^v y} is a sum of y block sums σ_v(l). ∎

**Lemma 2.3 (reflection).** For t ≥ 1 and 0 ≤ n ≤ p^t − 1: H′_{p^t−1−n} − H′_n ≡ −p^t Σ′_{n<μ<p^t} μ^{−2} (mod p^{2t}); in particular H′_{p^t−1−n} ≡ H′_n (mod p^t). For s ≥ 1, t ≥ 1 and 0 ≤ k ≤ p^t: H′_{(p^t−k)p^s} − H′_{kp^s} ≡ 0 (mod p^{t+2s}).
Proof. With μ := p^t − λ, H′_{p^t−1−n} = Σ′_{n<μ<p^t} 1/(p^t−μ) = −Σ′_{n<μ<p^t} (1/μ)(1 − p^t/μ)^{−1} = −(H′_{p^t−1} − H′_n) − p^t Σ′_{n<μ<p^t} μ^{−2} − p^{2t}(integral), and H′_{p^t−1} = H′_{p^t} ≡ 0 (mod p^{2t}) by Lemma 2.2. Same computation with μ := p^{t+s} − λ for the second claim: H′_{(p^t−k)p^s} = −(H′_{p^{t+s}} − H′_{kp^s}) − p^{t+s}Σ′_{kp^s<μ<p^{t+s}} μ^{−2} − p^{2(t+s)}(integral); the middle sum runs over full p^s-blocks, so it is ≡ 0 (mod p^s) by Lemma 2.1, and H′_{p^{t+s}} ≡ 0 (mod p^{2t+2s}). ∎

**Lemma 2.4 (block shift).** Let t ≥ 1, i ≥ 0, and write n = ip^t + n̄ with 0 ≤ n̄ < p^t. Then H′_n ≡ H′_{ip^t} + H′_{n̄} (mod p^t), and for any d ≥ 1, 1/(ip^t + λ)^d ≡ λ^{−d} (mod p^t) for p ∤ λ.
Proof. H′_n − H′_{ip^t} = Σ′_{λ≤n̄} 1/(ip^t+λ) and 1/(ip^t+λ) ≡ 1/λ (mod p^t). ∎

**Lemma 2.5 (double harmonic sums, first kind; Beukers, Lemma 4(i), new proof).** For s ≥ 0, t ≥ 0, i ≥ 0:
 Σ_{n∈B_t(i)} σ_s(n) H′_n ≡ 0 (mod p^{t+2s}).
Proof. For t = 0 this is σ_s(i)H′_i ≡ 0 (mod p^{2s}) (Lemma 2.2). Let t ≥ 1 and put t′ := t + s. Interchanging the summations, Σ_{n∈B_t(i)} σ_s(n)H′_n = Σ′_{k∈B_{t′}(i)} (1/k) H′_{[k/p^s]} =: Σ(i).
Base block i = 0, s ≥ 1 (the case s = 0 is treated at the end). The involution k ↦ p^{t′} − k of the units of [1, p^{t′}) satisfies [(p^{t′}−k)/p^s] = p^t − 1 − [k/p^s] (because s ≥ 1 and p ∤ k, so p^s ∤ k). Hence, with n(k) := [k/p^s],
 2Σ(0) = Σ′_k (1/k + 1/(p^{t′}−k)) H′_{n(k)} + Σ′_k (1/(p^{t′}−k)) (H′_{p^t−1−n(k)} − H′_{n(k)}).
First sum: 1/k + 1/(p^{t′}−k) = p^{t′}/(k(p^{t′}−k)) ≡ −p^{t′}k^{−2} (mod p^{2t′}), and Σ′_{k<p^{t′}} k^{−2}H′_{n(k)} = Σ_{n<p^t} H′_n · Σ′_{k∈B_s(n)} k^{−2} ≡ 0 (mod p^s) by Lemma 2.1. So the first sum is ≡ 0 (mod p^{t′+s}) = (mod p^{t+2s}). Second sum: by Lemma 2.3 the bracket is −p^t Σ′_{n<μ<p^t} μ^{−2} + p^{2t}(integral), and grouping k by n = n(k), Σ′_{k∈B_s(n)} 1/(p^{t′}−k) = Σ′_{κ′<p^s} 1/((p^t−1−n)p^s + κ′) = σ_s(p^t−1−n) ≡ 0 (mod p^{2s}) (Lemma 2.2). So the second sum is ≡ 0 (mod p^{t+2s}). Since 2 is a unit, Σ(0) ≡ 0 (mod p^{t+2s}).
Base block, s = 0. Now n(k) = k and the involution gives n(p^t − k) = p^t − k = (p^t − 1 − k) + 1, so H′_{p^t−k} = H′_{p^t−1−k} + 1/(p^t−k). Hence 2Σ′_{k<p^t}(1/k)H′_k = Σ′_k (p^t/(k(p^t−k)))H′_k + Σ′_k (1/(p^t−k))(H′_{p^t−1−k} − H′_k) + Σ′_k 1/(p^t−k)². The first sum is ≡ 0 (mod p^t) (integral summands times p^t); the second is ≡ 0 (mod p^t) by Lemma 2.3 (the bracket is p^t times an integer); the third equals Σ′_{k<p^t} k^{−2} ≡ 0 (mod p^t) by Lemma 2.1. So Σ(0) ≡ 0 (mod p^t), which is the claim for s = 0.
General block (i ≥ 1), any s ≥ 0. Start from Σ(i) = Σ_{n∈B_t(i)} σ_s(n)H′_n and write n = ip^t + n̄ (0 ≤ n̄ < p^t). Two expansions, both exact with integral remainders:
 (α) H′_{ip^t+n̄} = H′_{ip^t} + Σ′_{λ≤n̄} 1/(ip^t+λ) = H′_{ip^t} + H′_{n̄} − ip^t S_2(n̄) + p^{2t}η(n̄), η(n̄) ∈ ℤ_p (from 1/(ip^t+λ) = 1/λ − ip^t/λ² + (ip^t)²/(λ²(ip^t+λ)));
 (β) σ_s(ip^t+n̄) = Σ′_{κ<p^s} 1/((ip^t+n̄)p^s + κ) = σ_s(n̄) − ip^{t′} τ_s(n̄) + p^{2t′}θ(n̄), θ(n̄) ∈ ℤ_p, where τ_s(n̄) := Σ′_{k̄∈B_s(n̄)} k̄^{−2} ≡ 0 (mod p^s) by Lemma 2.1 (for s = 0, τ_0(n̄) = n̄^{−2} and the congruence is empty); moreover σ_s(ip^t+n̄) ≡ 0 (mod p^{2s}) by Lemma 2.2.
Multiplying (α) by σ_s(ip^t+n̄) and summing over n̄ < p^t gives four pieces: H′_{ip^t}·σ_{t′}(i) ≡ 0 (mod p^{2t+2t′}) (Lemma 2.2 twice); Σ_{n̄} σ_s(ip^t+n̄)H′_{n̄} = Σ(0) − ip^{t′}Σ_{n̄}τ_s(n̄)H′_{n̄} + p^{2t′}(integral) ≡ 0 (mod p^{t+2s}), because Σ(0) ≡ 0 (base block), p^{t′}τ_s(n̄) ≡ 0 (mod p^{t′+s}) = (mod p^{t+2s}), and 2t′ ≥ t + 2s; −ip^t Σ_{n̄} σ_s(ip^t+n̄)S_2(n̄) ≡ 0 (mod p^{t+2s}); and p^{2t}Σ_{n̄}σ_s(ip^t+n̄)η(n̄) ≡ 0 (mod p^{2t+2s}). Hence Σ(i) ≡ 0 (mod p^{t+2s}). ∎

**Lemma 2.6 (double harmonic sums, second kind; Beukers, Lemma 4(ii), strong form).** For s ≥ 0, t ≥ 0, i ≥ 0:
 Σ′_{k∈B_t(i)} (1/k) H′_{kp^s} ≡ 0 (mod p^{t+2s}).
Proof. For s = 0 this is Lemma 2.5 with s = 0. Let s ≥ 1; t = 0 is Lemma 2.2. Base block i = 0, t ≥ 1: by the involution k ↦ p^t − k, 2Σ′_{k<p^t}(1/k)H′_{kp^s} = Σ′_k (p^t/(k(p^t−k))) H′_{kp^s} + Σ′_k (1/(p^t−k))(H′_{(p^t−k)p^s} − H′_{kp^s}); the first sum is ≡ 0 (mod p^{t+2s}) since H′_{kp^s} ≡ 0 (mod p^{2s}), the second by Lemma 2.3. General block: k = ip^t + k̄, 1/k = 1/k̄ − ip^tk̄^{−2} + p^{2t}(integral), and H′_{kp^s} = H′_{ip^{t+s}} + Σ′_{λ≤k̄p^s} 1/(ip^{t+s}+λ) = H′_{ip^{t+s}} + H′_{k̄p^s} − ip^{t+s}S_2(k̄p^s) + p^{2(t+s)}(integral), with H′_{ip^{t+s}} ≡ 0 (mod p^{2(t+s)}) and S_2(k̄p^s) ≡ 0 (mod p^s) (Lemma 2.1). Multiplying out, every term except Σ′_{k̄}(1/k̄)H′_{k̄p^s} (the base block) is ≡ 0 (mod p^{t+2s}): the corrections to 1/k carry p^t and meet H′_{k̄p^s} ≡ 0 (mod p^{2s}); the correction −ip^{t+s}S_2 carries p^{t+2s}. ∎

**Lemma 2.7 (carry-restricted sums).** For t ≥ 1, blocks i, i′ ≥ 0, c ∈ {0,1}, and n̄ := n mod p^t, j̄ := j mod p^t, define the cell
 Cell_t(i,i′;c) := {(n,j) : n ∈ B_t(i), j ∈ B_t(i′), p ∤ j, [ n̄ + j̄ ≥ p^t ] = c}.
 (Y) For s′ ≥ 0: Σ_{(n,j)∈Cell_t(i,i′;c)} σ_{s′}(n)/j ≡ 0 (mod p^{2s′+t}).
 (B) Σ_{(k,j)∈Cell_t(i,i′;c), p∤k} 1/(kj) ≡ 0 (mod p^t).
Proof. (Y) Summing over both values of c gives Σ_{n∈B_t(i)}σ_{s′}(n)·Σ′_{j∈B_t(i′)}1/j = σ_{s′+t}(i)σ_t(i′) ≡ 0 (mod p^{2s′+2t+2t}) (Lemma 2.2), so it suffices to treat c = 1, i.e. j̄ ≥ p^t − n̄ (which forces n̄ ≥ 1). By Lemma 2.4, 1/j = 1/j̄ + p^t(integral), and the correction contributes ≡ 0 (mod p^{t+2s′}) because σ_{s′}(n) ≡ 0 (mod p^{2s′}). The main part is Σ_{n∈B_t(i)} σ_{s′}(n)·(H′_{p^t−1} − H′_{p^t−1−n̄}); H′_{p^t−1} ≡ 0 (mod p^{2t}) and Σ_nσ_{s′}(n) = σ_{s′+t}(i), so the first piece is ≡ 0 (mod p^{2t+2s′+2t}); by Lemma 2.3, H′_{p^t−1−n̄} = H′_{n̄} + p^t(integral) = H′_n − H′_{ip^t} + p^t(integral) (Lemma 2.4), and the p^t-corrections again meet σ_{s′}(n) ≡ 0 (mod p^{2s′}). What remains is −Σ_{n∈B_t(i)}σ_{s′}(n)H′_n + H′_{ip^t}σ_{s′+t}(i), ≡ 0 (mod p^{2s′+t}) by Lemma 2.5 and Lemma 2.2.
(B) Both carries together give σ_t(i)σ_t(i′) ≡ 0 (mod p^{4t}); take c = 1. Replace 1/k, 1/j by 1/k̄, 1/j̄ (corrections ≡ 0 mod p^t, all sums integral). Then Σ′_{k̄<p^t}(1/k̄)Σ′_{j̄≥p^t−k̄}1/j̄ = Σ′_{k̄}(1/k̄)(H′_{p^t−1} − H′_{p^t−1−k̄}) ≡ −Σ′_{k̄<p^t} H′_{k̄}/k̄ ≡ 0 (mod p^t) by Lemmas 2.3 and 2.6 (s = 0, i = 0). ∎

## 3. Block inductions and kernel towers

**Lemma 3.1 (one-index block induction; Beukers, Lemma 3; Straub, Lemma 5.6).** Let (T_u)_{u≥0} be functions ℤ_{≥0} → ℤ_p with the *tower property*
 T_u(k) ≡ T_{u−1}([k/p]) (mod p^u) for all u ≥ 1 and k ≥ 0.
Let a_k ∈ ℤ_p (k ≥ 0) satisfy Σ_{k∈B_t(l)} a_k ≡ 0 (mod p^t) for all t ≥ 0, l ≥ 0. Then Σ_{k∈B_s(l)} a_k T_s(k) ≡ 0 (mod p^s) for all s ≥ 0, l ≥ 0; hence also Σ_{k<mp^s} a_kT_s(k) ≡ 0 (mod p^s).
Proof (induction on s; s = 0 trivial). Σ_{k∈B_s(l)} a_kT_s(k) ≡ Σ_{q∈B_{s−1}(l)} (Σ_{k∈B_1(q)} a_k)·T_{s−1}(q) (mod p^s). The hypothesis at t = 1 makes ā_q := p^{−1}Σ_{k∈B_1(q)} a_k integral, and Σ_{q∈B_t(l′)} ā_q = p^{−1}Σ_{k∈B_{t+1}(l′)} a_k ≡ 0 (mod p^t). By induction Σ_{q∈B_{s−1}(l)} ā_q T_{s−1}(q) ≡ 0 (mod p^{s−1}). ∎
(The functions T_u may change their form from level to level; only the tower property is used. Moreover the tower property is only needed at arguments where the weights are nonzero: if a_k = 0 for p | k, it suffices that T_s(k) ≡ T_{s−1}([k/p]) (mod p^s) for p ∤ k, since T_s can be redefined as T_{s−1}([k/p]) on the multiples of p without changing the sum. This is Beukers' Lemma 3(ii).)

**Lemma 3.2 (two-index block induction with carries).** Let (T_u^{(δ)})_{u≥0, δ∈{0,1}} be functions ℤ_{≥0}² → ℤ_p with the tower property
 T_u^{(δ)}(q,q′) ≡ T_{u−1}^{(δ′)}([q/p],[q′/p]) (mod p^u), δ′ := [ (q mod p) + (q′ mod p) + δ ≥ p ],  for all u ≥ 1.
For t ≥ 1 and labels define the cells Cell_t(i,i′;c) := {(q,q′,δ) : q ∈ B_t(i), q′ ∈ B_t(i′), [ (q mod p^t) + (q′ mod p^t) + δ ≥ p^t ] = c}. Let a^{(δ)}_{q,q′} ∈ ℤ_p satisfy Σ_{(q,q′,δ)∈Cell_t(i,i′;c)} a^{(δ)}_{q,q′} ≡ 0 (mod p^t) for all t ≥ 1, i, i′ ≥ 0, c ∈ {0,1}. Then for all s ≥ 0, l, l′ ≥ 0:
 Σ_{q∈B_s(l), q′∈B_s(l′), δ} a^{(δ)}_{q,q′} T_s^{(δ)}(q,q′) ≡ 0 (mod p^s).
Proof (induction on s; s = 0 trivial). Replace T_s^{(δ)}(q,q′) by T_{s−1}^{(δ′)}(q₁,q₁′) (q₁ = [q/p], q₁′ = [q′/p]) modulo p^s and collect terms with the same (q₁,q₁′,δ′): the coefficient is Σ over the level-1 cell {(q,q′,δ) : [q/p]=q₁, [q′/p]=q₁′, [(q mod p)+(q′ mod p)+δ ≥ p] = δ′}, which is ≡ 0 (mod p) by hypothesis, so ā^{(δ′)}_{q₁,q₁′} := p^{−1}·(that sum) is integral. Carries compose: (q mod p^t) + (q′ mod p^t) + δ = p[(q₁ mod p^{t−1}) + (q₁′ mod p^{t−1}) + δ′] + ((q mod p)+(q′ mod p)+δ − pδ′) with the last bracket in [0, p−1], so [(q mod p^t)+(q′ mod p^t)+δ ≥ p^t] = [(q₁ mod p^{t−1})+(q₁′ mod p^{t−1})+δ′ ≥ p^{t−1}]. Hence the cell sums of ā at level t−1 are p^{−1} times cell sums of a at level t, ≡ 0 (mod p^{t−1}), and induction applies. ∎
In the applications the top-level weights carry the label δ = 0 only (no carry enters the lowest digit) and vanish unless p ∤ j, and the top-level kernel is a single function T^{(0)}_s; the labels appear from the first reduction on. With these restrictions the cells of this lemma at the top level coincide with the cells Cell_t(i,i′;c) of Lemma 2.7 (same name, there defined for pairs (n,j) with p ∤ j), which is why Lemma 2.7 supplies exactly the hypothesis needed. As in Lemma 3.1, the tower property is only needed where the weights are nonzero (e.g. for p ∤ j when the weights vanish for p | j); this restriction to units is available only at the top level — the lower levels need the full tower property, which holds in every application.

**Kernels.** For u ≥ 0 put L_u := mp^u and define, for n, j, q, q′ ≥ 0 and δ ∈ {0,1},
 Ψ_u(n,j) := C(L_u−1,n)² · (−1)^n C(−L_u−1,n) · C(L_u−1,n+j)² · (−1)^j C(−L_u,j),
 K_u(n) := Σ_{j≥0} Ψ_u(n,j),
 Ξ_u^{(δ)}(q,q′) := C(L_u−1,q)² · (−1)^q C(−L_u−1,q) · C(L_u−1,q+q′+δ)² · (−1)^{q′} C(−L_u−1,q′),
 Ξ̂_u(n,j) := C(L_u−1,n)² · (−1)^n C(−L_u−1,n) · C(L_u−1,n+j)² · (−1)^{j−1} C(−L_u−1,j−1)   (for j ≥ 1).
All are integers; Ψ_u(n,j) = 0 unless n + j ≤ L_u − 1 (the factor C(L_u−1,n+j)), so K_u(n) is a finite sum and K_u(n) = 0 for n ≥ L_u.

**Lemma 3.3 (how the terms factor).** For k, j ≥ 0: S̃(N;k,j) = (N/(N+k))·Ψ_r(k,j). For p ∤ j and any n: Ψ_u(n,j) = (L_u/j)·Ξ̂_u(n,j).
Proof. C(N+k−1,k) = (−1)^kC(−N,k) and C(−N,k) = C(−N−1,k)·(−N)/(−N−k) (from C(a,k) = C(a−1,k)·a/(a−k)); similarly C(N+j−1,j) = (−1)^jC(−N,j). For the second claim, (−1)^jC(−L,j) = (−1)^j(−L/j)C(−L−1,j−1) = (L/j)(−1)^{j−1}C(−L−1,j−1). ∎

**Lemma 3.4 (towers).** Let u ≥ 1, L = L_u, L′ = L_{u−1}, q′ := [q/p], etc.
 (a) For p ∤ j: Ψ_u(q,j) ≡ 0 (mod p^u). For j = pj₁: Ψ_u(q,pj₁) ≡ Ψ_{u−1}([q/p], j₁) (mod p^u). Hence K_u(q) ≡ K_{u−1}([q/p]) (mod p^u): (K_u) is a tower.
 (b) Ξ_u^{(δ)}(q,q′) ≡ Ξ_{u−1}^{(δ′)}([q/p],[q′/p]) (mod p^u) with δ′ = [(q mod p)+(q′ mod p)+δ ≥ p]; and for p ∤ j, Ξ̂_u(n,j) ≡ Ξ_{u−1}^{(δ)}([n/p],[j/p]) (mod p^u) with δ = [(n mod p)+(j mod p) ≥ p]. So (Ξ̂_u at the top, then Ξ_{u−1}^{(·)}, Ξ_{u−2}^{(·)}, …) is a two-index tower in the sense of Lemma 3.2.
 (c) (moment kernels) For t ≥ 1 and u ≥ 0: K_u^{[t]}(q) := Σ_{j≥0} j^t Ψ_u(q,j) ≡ 0 (mod p^u).
 (d) (harmonically weighted kernels) For d ≥ 1 put K̃_u^{(d)}(q) := Σ_{j≥0} Ψ_u(q,j) H′_{p^d j}. Then K̃_u^{(d)}(q) ≡ K̃_{u−1}^{(d+1)}([q/p]) (mod p^u); so for any s₀ ≥ 0 and d₀ ≥ 1 the functions T_u := K̃_u^{(d₀+s₀−u)} (0 ≤ u ≤ s₀) form a tower in the sense of Lemma 3.1.
Proof. (a) For p ∤ j the factor (−1)^jC(−L,j) = (L/j)(−1)^{j−1}C(−L−1,j−1) is divisible by p^u. For j = pj₁ apply Lemma 1.2 factor by factor: C(L−1,q)² ≡ C(L′−1,q′)²; (−1)^qC(−L−1,q) ≡ (−1)^{q′}C(−L′−1,q′) (Lemma 1.2(a) with −m); C(L−1,q+pj₁)² ≡ C(L′−1,q′+j₁)² (because [(q+pj₁)/p] = q′ + j₁); (−1)^{pj₁}C(−L,pj₁) ≡ (−1)^{j₁}C(−L′,j₁) (Lemma 1.2(b) with −m, and (−1)^{pj₁} = (−1)^{j₁}). Summing over j: the unscaled j vanish mod p^u, the scaled ones give K_{u−1}(q′). (b) Same factor-by-factor reduction; for the coupled factor, [(q+q′+δ)/p] = [q/p]+[q′/p]+δ′ by the definition of δ′; for Ξ̂ use (−1)^{j−1}C(−L−1,j−1) ≡ (−1)^{[j/p]}C(−L′−1,[j/p]) (the consequence recorded after Lemma 1.2) and [(n+j)/p] = [n/p]+[j/p]+δ. (c) Induction on u; u = 0 is empty. For u ≥ 1: the unscaled j contribute ≡ 0 (mod p^u) by (a); the scaled j = pj₁ contribute p^t Σ_{j₁} j₁^t Ψ_u(q,pj₁) ≡ p^t K^{[t]}_{u−1}(q′) (mod p^{u+t}), and p^t·p^{u−1} ∈ p^uℤ_p by induction. (d) Unscaled j: Ψ_u(q,j) ≡ 0 (mod p^u) and H′ is integral; scaled j = pj₁: Ψ_u(q,pj₁) ≡ Ψ_{u−1}(q′,j₁) and H′_{p^d·pj₁} = H′_{p^{d+1}j₁} exactly. ∎
(The congruences (a), (b) with the stated signs were also checked by computer: `numerics/out/a376462_lemma_bank_checks.txt`, items A1–A3; (c): item B.)

**Lemma 3.5 (the one-level first-order model).** Let u ≥ 0, L := L_{u+1} = mp^{u+1}, and for x ≥ 0 let P_x := Π′_{λ≤x}(1 − L/λ), P̄_x := Π′_{λ≤x}(1 + L/λ). Then for all n, j₁ ≥ 0, exactly,
 Ψ_{u+1}(n, pj₁) = Ψ_u([n/p], j₁) · P_n² P̄_n P_{n+pj₁}² P̄_{pj₁},
and consequently Ψ_{u+1}(n,pj₁) ≡ Ψ_u([n/p],j₁)·(1 − L·ρ_u(n,j₁)) (mod p^{2u+2}), with
 ρ_u(n,j₁) := H′_n − H′_{pj₁} + 2H′_{n+pj₁}.
Proof. Lemma 1.1(i) with m and with −m, and Lemma 1.1(ii) with −m: C(L−1,n) = (−1)^{n−q}C(L′−1,q)P_n (q = [n/p]); (−1)^nC(−L−1,n) = (−1)^n·(−1)^{n−q}C(−L′−1,q)P̄_n = (−1)^qC(−L′−1,q)P̄_n; C(L−1,n+pj₁)² = C(L′−1,q+j₁)²P²_{n+pj₁} (the sign disappears in the square); (−1)^{pj₁}C(−L,pj₁) = (−1)^{j₁}C(−L′,j₁)P̄_{pj₁}. Multiply. The congruence is Lemma 1.3 with e_1 = −2H′_n + H′_n − 2H′_{n+pj₁} + H′_{pj₁} = −ρ_u(n,j₁) and L² ∈ p^{2u+2}ℤ_p. ∎

## 4. Class K

Let K̂_r(k) := Σ_{j₁≥0} Ψ_r(k,pj₁) (only scaled j). By Lemma 3.3, for p ∤ k,
 Σ_{j: p|j} S̃(N;k,j) = (N/(N+k)) K̂_r(k) = (N/k)·(1 + N/k)^{−1} K̂_r(k) = (N/k) K̂_r(k) − (N²/k²) K̂_r(k) + (N³/k³)(1+N/k)^{−1} K̂_r(k).
The last term is in p^{3r}ℤ_p. Hence
 Σ_K ≡ N·Σ′_{k<N} (1/k) K̂_r(k) − N²·Σ′_{k<N} (1/k²) K̂_r(k)  (mod p^{3r}).            (4.1)

**(4.a) The 1/k² term.** K̂_r(k) = Σ_{j₁}Ψ_r(k,pj₁) ≡ Σ_{j₁}Ψ_{r−1}([k/p],j₁) = K_{r−1}([k/p]) (mod p^r) by Lemma 3.4(a) (termwise in j₁), so (K̂_r, K_{r−1}, K_{r−2}, …) is a tower. With a_k := k^{−2} for p ∤ k and 0 otherwise, Σ_{k∈B_t(l)}a_k ≡ 0 (mod p^t) by Lemma 2.1. Lemma 3.1 gives Σ′_{k<N}(1/k²)K̂_r(k) ≡ 0 (mod p^r), so the second term of (4.1) is ≡ 0 (mod p^{3r}).

**(4.b) The 1/k term: reduction to A_{r−1}.** Define for 0 ≤ s ≤ r − 1
 A_s := Σ_{n<L_s} σ_{r−s}(n) K_s(n).
By Lemma 3.5 (u = r−1, L = N): K̂_r(k) = Σ_{j₁}Ψ_{r−1}(n′,j₁)·(1 − Nρ_{r−1}(k,j₁)) + N²(integral), n′ := [k/p]. Therefore
 Σ′_{k<N}(1/k)K̂_r(k) ≡ Σ_{n′<M} σ_1(n′)K_{r−1}(n′) − N·X̂ = A_{r−1} − N·X̂  (mod p^{2r}),   X̂ := Σ′_{k<N}(1/k) Σ_{j₁} Ψ_{r−1}(n′,j₁) ρ_{r−1}(k,j₁).   (4.2)
(We used Σ′_{k∈B_1(n′)}1/k = σ_1(n′).) Claim (4.b.1): X̂ ≡ 0 (mod p^r). Claim (4.b.2): A_{r−1} ≡ 0 (mod p^{2r}). Together with (4.a) and (4.1) they give Σ_K ≡ 0 (mod p^{3r}).

**Proof of (4.b.1).** Split ρ_{r−1}(k,j₁) = H′_k − H′_{pj₁} + 2H′_{k+pj₁} and X̂ = X̂₁ − X̂₂ + 2X̂₃ accordingly.
 • X̂₁ = Σ′_k (1/k)H′_k K_{r−1}(n′) = Σ_{n′} c_{n′}K_{r−1}(n′) with c_{n′} := Σ′_{k∈B_1(n′)} H′_k/k. By Lemma 2.6 (s = 0, t+1), Σ_{n′∈B_t(i)} c_{n′} = Σ′_{k∈B_{t+1}(i)} H′_k/k ≡ 0 (mod p^{t+1}); so a_{n′} := c_{n′}/p is integral with block sums ≡ 0 (mod p^t), and Lemma 3.1 (tower (K_u)) gives Σ_{n′}a_{n′}K_{r−1}(n′) ≡ 0 (mod p^{r−1}), i.e. X̂₁ ≡ 0 (mod p^r).
 • X̂₂ = Σ′_k (1/k) Σ_{j₁}Ψ_{r−1}(n′,j₁)H′_{pj₁} = Σ_{n′} σ_1(n′) K̃^{(1)}_{r−1}(n′). By Lemma 2.2, a_{n′} := σ_1(n′)/p² is integral and Σ_{n′∈B_t(i)}a_{n′} = σ_{t+1}(i)/p² ≡ 0 (mod p^{2t}). Lemma 3.1 with the tower of Lemma 3.4(d) gives X̂₂ ≡ 0 (mod p^{2+r−1}).
 • X̂₃ = Σ′_k (1/k)Σ_{j₁}Ψ_{r−1}(n′,j₁)H′_{k+pj₁}. Exactly, H′_{k+pj₁} = H′_{pj₁} + Σ′_{λ≤k} 1/(pj₁+λ), and in ℤ_p, 1/(pj₁+λ) = Σ_{t≥0} (−pj₁)^t λ^{−t−1} (convergent). Hence X̂₃ = X̂₂ + Σ_{t≥0} (−p)^t Σ′_k (1/k) S_{t+1}(k) K^{[t]}_{r−1}(n′), where K^{[0]} = K. The t = 0 term is X̂₁ ≡ 0 (mod p^r). For t ≥ 1, S_{t+1}(k) is integral and K^{[t]}_{r−1}(n′) ≡ 0 (mod p^{r−1}) by Lemma 3.4(c), so the t-th term is ≡ 0 (mod p^{t+r−1}) ⊂ p^rℤ_p; the series converges and all its terms lie in p^rℤ_p. So X̂₃ ≡ 0 (mod p^r). ∎

**Proof of (4.b.2) — the induction A_0 ≡ A_1 ≡ … ≡ A_{r−1} ≡ 0 (mod p^{2r}).**
Base: A_0 = Σ_{n<m} σ_r(n)K_0(n) ≡ 0 (mod p^{2r}) by Lemma 2.2.
Step s → s+1 (0 ≤ s ≤ r−2). Let L := L_{s+1}, q := [n/p]. Splitting the j-sum into scaled and unscaled j and using Lemma 3.5 for the former and Lemma 3.3 for the latter, for every n,
 K_{s+1}(n) = Σ_{j₁} Ψ_{s+1}(n,pj₁) + Σ′_j Ψ_{s+1}(n,j) = Σ_{j₁} Ψ_s(q,j₁)(1 − Lρ_s(n,j₁)) + L·Σ′_j (1/j) Ξ̂_{s+1}(n,j) + p^{2s+2}(integral),
using Lemma 3.5 for the scaled j and Lemma 3.3 for the unscaled j (where Ξ̂_{s+1}(n,j) is an integer). Multiply by σ_{r−s−1}(n) ≡ 0 (mod p^{2(r−s−1)}) (Lemma 2.2) and sum over n < L_{s+1}; the error is ≡ 0 (mod p^{2(r−s−1)+2s+2}) = (mod p^{2r}). Since Σ_{n∈B_1(q)} σ_{r−s−1}(n) = σ_{r−s}(q) and Σ_{j₁}Ψ_s(q,j₁) = K_s(q),
 A_{s+1} ≡ A_s − mp^{s+1}·X_s + mp^{s+1}·Y_s  (mod p^{2r}),
 X_s := Σ_{n<L_{s+1}} σ_{r−s−1}(n) Σ_{j₁} Ψ_s(q,j₁) ρ_s(n,j₁),   Y_s := Σ_{n<L_{s+1}} σ_{r−s−1}(n) Σ′_{j} (1/j) Ξ̂_{s+1}(n,j).
It remains to show X_s ≡ 0 and Y_s ≡ 0 (mod p^{2r−s−1}). Put s′ := r−s−1 ≥ 1.
 • X_s = X_{s,1} − X_{s,2} + 2X_{s,3} with the three parts of ρ_s(n,j₁) = H′_n − H′_{pj₁} + 2H′_{n+pj₁}.
  X_{s,1} = Σ_n σ_{s′}(n)H′_n K_s(q) = Σ_q c_q K_s(q), c_q := Σ_{n∈B_1(q)} σ_{s′}(n)H′_n. By Lemma 2.5 (with s′ and t+1), Σ_{q∈B_t(i)} c_q = Σ_{n∈B_{t+1}(i)} σ_{s′}(n)H′_n ≡ 0 (mod p^{t+1+2s′}); so a_q := c_q/p^{2s′+1} is integral with block sums ≡ 0 (mod p^t), and Lemma 3.1 (tower (K_u)) gives Σ_q a_qK_s(q) ≡ 0 (mod p^s): X_{s,1} ≡ 0 (mod p^{2s′+1+s}) = (mod p^{2r−s−1}).
  X_{s,2} = Σ_n σ_{s′}(n) Σ_{j₁}Ψ_s(q,j₁)H′_{pj₁} = Σ_q σ_{s′+1}(q) K̃^{(1)}_s(q). a_q := σ_{s′+1}(q)/p^{2s′+2} is integral with block sums ≡ 0 (mod p^{2t}) (Lemma 2.2); Lemma 3.1 with the tower of Lemma 3.4(d) gives X_{s,2} ≡ 0 (mod p^{2s′+2+s}) ⊂ p^{2r−s−1}ℤ_p.
  X_{s,3} = Σ_n σ_{s′}(n)Σ_{j₁}Ψ_s(q,j₁)H′_{n+pj₁} = X_{s,2} + Σ_{t≥0}(−p)^t Σ_n σ_{s′}(n) S_{t+1}(n) K^{[t]}_s(q) (same expansion as for X̂₃). The t = 0 term is X_{s,1}; for t ≥ 1 the term is ≡ 0 (mod p^{t+2s′+s}) ⊂ p^{2r−s−1}ℤ_p by Lemmas 2.2 and 3.4(c). So X_{s,3} ≡ 0 (mod p^{2r−s−1}).
 • Y_s: apply Lemma 3.2 at level s+1 to the tower (Ξ̂_{s+1}; Ξ^{(·)}_s; Ξ^{(·)}_{s−1}; …) of Lemma 3.4(b), with top-level weights a^{(0)}_{n,j} := p^{−2s′}σ_{s′}(n)/j for p ∤ j (0 otherwise; a^{(1)} := 0), which are integral by Lemma 2.2. The cell hypothesis at level t ≥ 1 is Σ_{(n,j)∈Cell_t(i,i′;c)} σ_{s′}(n)/j ≡ 0 (mod p^{2s′+t}), which is Lemma 2.7(Y). Hence Σ_{n,j} a^{(0)}_{n,j}Ξ̂_{s+1}(n,j) ≡ 0 (mod p^{s+1}), i.e. Y_s ≡ 0 (mod p^{2s′+s+1}) = (mod p^{2r−s−1}). ∎
This proves (K).

## 5. Class J

For p ∤ j and k = pk₁, Lemma 3.3 applied to the j-factor gives S̃(N;pk₁,j) = (N/(N+j))·Φ_r(pk₁,j) with
 Φ_u(k,j) := C(L_u−1,k)² · (−1)^k C(−L_u,k) · C(L_u−1,k+j)² · (−1)^j C(−L_u−1,j).
Everything in §4 goes through with (Ψ, harmonic index n, kernel index j) replaced by (Φ, harmonic index j, kernel index k), because Φ has the same four properties: (i) for p ∤ k, Φ_u(k,j) = (L_u/k)·Ξ̂′_u(k,j) with Ξ̂′_u(k,j) := C(L_u−1,k)²(−1)^{k−1}C(−L_u−1,k−1)C(L_u−1,k+j)²(−1)^jC(−L_u−1,j), and Ξ̂′_u(k,j) ≡ Ξ^{(δ)}_{u−1}([k/p],[j/p]) (mod p^u) with the same two-index tower Ξ (Lemma 3.4(b) applied with the arguments in this order; Ξ is not symmetric in (q,q′), but Lemma 3.2 treats the two indices symmetrically through its cells, and the displayed congruence was tested exactly, `numerics/out/rereview_shifted_towers.txt`, item sec5(i)); (ii) Φ_{u+1}(pk₁, j) = Φ_u(k₁,[j/p])·P̄_{pk₁}P²_{pk₁}P²_{pk₁+j}P̄_j exactly (Lemma 1.1 factor by factor, as in Lemma 3.5), so Φ_{u+1}(pk₁,j) ≡ Φ_u(k₁,[j/p])(1 − L_{u+1}ρ′_u(j,k₁)) (mod p^{2u+2}) with ρ′_u(j,k₁) = −H′_j + H′_{pk₁} + 2H′_{j+pk₁} (the harmonic index j now carries only the factor (−1)^jC(−L−1,j), whence −H′_j instead of +H′_n, and the kernel index k₁ carries C(L−1,pk₁)²(−1)^{pk₁}C(−L,pk₁), whence +H′_{pk₁}); so X̂′ = −X̂′₁ + X̂′₂ + 2X̂′₃ and X′_s = −X′_{s,1} + X′_{s,2} + 2X′_{s,3} with the three pieces of the same three types as in §4, each ≡ 0 to the required order by the same lemmas, so the signs are immaterial; (iii) the towers: K′_u(j) := Σ_k Φ_u(k,j) satisfies K′_u(j) ≡ K′_{u−1}([j/p]) (mod p^u) (unscaled k vanish mod p^u by (i), scaled k reduce by Lemma 1.2; no carry since pk₁ has lowest digit 0), the moment kernels Σ_k k^tΦ_u(k,j) ≡ 0 (mod p^u) for t ≥ 1, and Σ_kΦ_u(k,j)H′_{p^dk} ≡ Σ_{k₁}Φ_{u−1}(k₁,[j/p])H′_{p^{d+1}k₁} (mod p^u); (iv) the top-level decomposition Σ_J ≡ N Σ′_j (1/j)K̂′_r(j) − N²Σ′_j(1/j²)K̂′_r(j) (mod p^{3r}) with K̂′_r(j) := Σ_{k₁}Φ_r(pk₁,j). With A′_s := Σ_{j<L_s} σ_{r−s}(j)K′_s(j) the induction of §4 applies verbatim (the pieces X′_{s,1}, X′_{s,2}, X′_{s,3} use Lemmas 2.5, 2.2, 3.4-type (c),(d) for Φ; Y′_s uses Lemma 2.7(Y) with the roles of the two indices in the cell exchanged, which is harmless because the carry condition is symmetric). This proves (J). (The class-J dissection was also measured with the coefficient ρ′ above: `numerics/out/a376462_classJ_dissection.txt`, every piece vanishes to the required order.)

## 6. Class B

For p ∤ k, p ∤ j, by Lemma 3.3 twice, S̃(N;k,j) = (N/(N+k))·(N/j)·Ξ̂_r(k,j) = (N²/(kj))·Ξ̂_r(k,j) − (N³/(k²j))(1+N/k)^{−1}Ξ̂_r(k,j), so
 Σ_B ≡ N² Σ′_{k,j} Ξ̂_r(k,j)/(kj)  (mod p^{3r}).
Apply Lemma 3.2 at level r to the tower (Ξ̂_r; Ξ^{(·)}_{r−1}; …) with weights a^{(0)}_{k,j} := 1/(kj) for p ∤ k, p ∤ j (0 otherwise): the cell hypothesis is Lemma 2.7(B). Hence Σ′_{k,j}Ξ̂_r(k,j)/(kj) ≡ 0 (mod p^r) and Σ_B ≡ 0 (mod p^{3r}). This proves (B).

## 7. Class S

Let k = pk′, j = pj′ (k′, j′ ≥ 0). By Lemma 1.1 (with m and −m, as in Lemma 3.5) and C(N+x−1,x) = (−1)^xC(−N,x), exactly
 S̃(N;pk′,pj′) = S̃(M;k′,j′) · E(k′,j′),  E := P_{pk′}² P̄_{pk′} P_{p(k′+j′)}² P̄_{pj′},
with P, P̄ as in Lemma 3.5 for L = N (the signs cancel: pk′ − k′ is even). Summing, Σ_S − a(M−1) = Σ_{k′,j′} S̃(M;k′,j′)(E − 1).

**Step 1 (second and higher order are negligible termwise).** By Lemma 1.3, E − 1 = −N·ρ_S + N²e_2 + Σ_{d≥3}N^de_d with ρ_S := H′_{pk′} + 2H′_{p(k′+j′)} − H′_{pj′}, all e_d integral, and v(e_2) ≥ min(2v(ρ_S), v(S_2(pk′)), v(S_2(p(k′+j′))), v(S_2(pj′))). Put a := v(k′), b := v(j′) (a = ∞ if k′ = 0, etc.). For x ∈ {k′, k′+j′, j′} with x ≥ 1, v_p(px) ≥ 1 + min(a,b), so S_2(px) ≡ 0 (mod p^{1+min(a,b)}) (Lemma 2.1) and ρ_S ≡ 0 (mod p^{2+2min(a,b)}) (Lemma 2.2); hence v(N²e_2) ≥ 2r + 1 + min(a,b). On the other side, for k′ ≥ 1, C(M+k′−1,k′) = (M/k′)·C(M+k′−1,k′−1) is divisible by p^{(r−1−a)⁺}, and likewise C(M+j′−1,j′) by p^{(r−1−b)⁺}; so v(S̃(M;k′,j′)) ≥ (r−1−a)⁺ + (r−1−b)⁺ ≥ (r−1−min(a,b))⁺. Therefore v(S̃(M;k′,j′)N²e_2) ≥ 2r + 1 + min(a,b) + (r−1−min(a,b))⁺ ≥ 3r (if k′ = j′ = 0 then E = 1). For d ≥ 3, v(N^de_d) ≥ 3r. Hence
 Σ_S − a(M−1) ≡ −N·T_S  (mod p^{3r}),  T_S := Σ_{k′,j′} S̃(M;k′,j′) ρ_S(k′,j′),
and it remains to show T_S ≡ 0 (mod p^{2r}).

**Step 2 (decoupling the coupled harmonic sum).** Exactly, H′_{p(k′+j′)} − H′_{pk′} = Σ′_{μ≤pj′} 1/(pk′+μ) = H′_{pj′} − pk′·Z(k′,j′), Z := Σ′_{μ≤pj′} 1/(μ(μ+pk′)) ∈ ℤ_p. So ρ_S = 3H′_{pk′} + H′_{pj′} − 2pk′Z. Claim: v(Z) ≥ 1 + b (for j′ ≥ 1; Z = 0 if j′ = 0). Indeed Z = Σ_{t≥0} (−pk′)^t S_{t+2}(pj′) (convergent in ℤ_p), and by Lemma 2.1, S_{t+2}(pj′) ≡ 0 (mod p^{1+b−e(t+2)}) (pj′ = p^{1+b}·(unit)·…, a union of full p^{1+b}-blocks); the t-th term thus has valuation ≥ t(1+a) + 1 + b − e(t+2) ≥ 1 + b + t − e(t+2), and t − e(t+2) ≥ 0 for all t ≥ 0 (e(t+2) = 0 unless (p−1) | t+2, which forces t + 2 ≥ p − 1 ≥ 4, and then e(t+2) = 1 + v_p(t+2) ≤ 1 + log_p(t+2) ≤ t). Consequently v(N·pk′Z·S̃(M;k′,j′)) ≥ r + 1 + a + 1 + b + (r−1−a)⁺ + (r−1−b)⁺ ≥ 3r, so
 T_S ≡ 3·T_1 + T_2  (mod p^{2r}),  T_1 := Σ_{k′,j′} S̃(M;k′,j′)H′_{pk′},  T_2 := Σ_{k′,j′} S̃(M;k′,j′)H′_{pj′}.
(Numerically: `numerics/out/a376462_final_lemma_checks.txt`, item (3).)

**Step 3 (T_1 ≡ 0 (mod p^{2r}); Beukers' stratification).** Write T_1 = Σ_{k′≥1} H′_{pk′}·C(M−1,k′)²C(M+k′−1,k′)·G_1(k′), G_1(k′) := Σ_{j′} C(M−1,k′+j′)²C(M+j′−1,j′). Stratify by σ := v_p(pk′) ≥ 1, k′ = p^{σ−1}κ with p ∤ κ.
 If σ ≥ r: H′_{pk′} ≡ 0 (mod p^{2σ}) ⊂ p^{2r}ℤ_p (Lemma 2.2) and the other factors are integers: these terms are ≡ 0 (mod p^{2r}).
 If 1 ≤ σ ≤ r−1: C(M+k′−1,k′) = (M/k′)C(M+k′−1,k′−1) = (mp^{r−σ}/κ)·(−1)^{k′−1}C(−M−1,k′−1). Reduce the remaining factors σ−1 times by Lemma 1.2 (levels r−1, r−2, …, r−σ+1, so modulo p^{r−σ+1} ⊂ p^{r−σ}ℤ_p): C(M−1,k′)² ≡ C(mp^{r−σ}−1,κ)²; (−1)^{k′−1}C(−M−1,k′−1) ≡ (−1)^{κ−1}C(−mp^{r−σ}−1,κ−1) (since [(p^{σ−1}κ−1)/p^{σ−1}] = κ−1 and the intermediate floors are p^{σ−1−i}κ − 1); and G_1(k′) ≡ G_1^{(r−σ)}(κ) where, for u ≥ 0, G_1^{(u)}(x) := Σ_{j} C(mp^u−1,x+j)²C(mp^u+j−1,j) — the latter because (G_1^{(u)}) is a tower: for p ∤ j the factor C(mp^u+j−1,j) = (mp^u/j)C(mp^u+j−1,j−1) is ≡ 0 (mod p^u), and for j = pj₁, C(mp^u−1,x+pj₁)² ≡ C(mp^{u−1}−1,[x/p]+j₁)² and C(mp^u+pj₁−1,pj₁) = (−1)^{pj₁}C(−mp^u,pj₁) ≡ (−1)^{j₁}C(−mp^{u−1},j₁) = C(mp^{u−1}+j₁−1,j₁) (mod p^u), so G_1^{(u)}(x) ≡ G_1^{(u−1)}([x/p]) (mod p^u). The reduction errors are O(p^{r−σ+1}) and meet the explicit p^{r−σ} and H′_{pk′} ≡ 0 (mod p^{2σ}), so they are ≡ 0 (mod p^{2r}). Hence the stratum is
 ≡ mp^{r−σ} Σ′_{κ<mp^{r−σ}} (1/κ) H′_{p^σκ} R^{(r−σ)}(κ)  (mod p^{2r}),  R^{(u)}(κ) := C(mp^u−1,κ)²(−1)^{κ−1}C(−mp^u−1,κ−1)G_1^{(u)}(κ).
 Put a_κ := p^{−2σ}(1/κ)H′_{p^σκ} for p ∤ κ (0 otherwise): integral by Lemma 2.2, and Σ_{κ∈B_t(i)} a_κ ≡ 0 (mod p^t) by Lemma 2.6 (with s = σ). The kernel: for p ∤ κ, R^{(u)}(κ) ≡ R̂^{(u−1)}([κ/p]) (mod p^u) with R̂^{(w)}(q) := C(mp^w−1,q)²(−1)^qC(−mp^w−1,q)G_1^{(w)}(q) (Lemma 1.2 and the consequence after it), and (R̂^{(w)})_w is a tower (Lemma 1.2 and the tower property of G_1). Lemma 3.1 (with the top function R^{(r−σ)} on the units and the tower R̂ below it) gives Σ′_κ a_κR^{(r−σ)}(κ) ≡ 0 (mod p^{r−σ}). The stratum is therefore ≡ 0 (mod p^{(r−σ)+2σ+(r−σ)}) = (mod p^{2r}). Summing the strata, T_1 ≡ 0 (mod p^{2r}).

**Step 4 (T_2 ≡ 0 (mod p^{2r})).** Write T_2 = Σ_{j′≥1} H′_{pj′}·C(M+j′−1,j′)·G_2(j′), G_2(j′) := Σ_{k′} C(M−1,k′)²C(M+k′−1,k′)C(M−1,k′+j′)². Stratify by σ := v_p(pj′), j′ = p^{σ−1}ι; the strata with σ ≥ r vanish as before; for σ ≤ r−1, C(M+j′−1,j′) = (mp^{r−σ}/ι)·(−1)^{j′−1}C(−M−1,j′−1) with (−1)^{j′−1}C(−M−1,j′−1) ≡ (−1)^{ι−1}C(−mp^{r−σ}−1,ι−1) (mod p^{r−σ}) (σ−1 reductions by Lemma 1.2), and G_2(j′) ≡ G_2^{(r−σ)}(ι) (mod p^{r−σ}) with G_2^{(u)}(y) := Σ_k C(mp^u−1,k)²C(mp^u+k−1,k)C(mp^u−1,k+y)², a tower in y (unscaled k vanish mod p^u through C(mp^u+k−1,k) = (mp^u/k)·…; scaled k = pk₁ reduce by Lemma 1.2 with [(pk₁+y)/p] = k₁+[y/p]). The rest is identical to Step 3 (Lemma 2.6 with s = σ, Lemma 3.1), giving T_2 ≡ 0 (mod p^{2r}).

Hence T_S ≡ 0 (mod p^{2r}), Σ_S ≡ a(M−1) (mod p^{3r}), which is (S). ∎

**Conclusion.** a(N−1) − a(M−1) = (Σ_S − a(M−1)) + Σ_K + Σ_J + Σ_B ≡ 0 (mod p^{3r}). The case r = 1 is included: the induction of §4 is then vacuous (only the base A_0 ≡ 0 (mod p²) and X̂ ≡ 0 (mod p) are used), every stratum of §7 has σ ≥ 1 = r, and §6 uses Lemma 3.2 at level 1 — this reproduces the r = 1 proof of the first-congruence note. Nothing used p ∤ m (the block lemmas are applied over m full blocks for arbitrary m, and the exponents (·)⁺ and the strata σ ≥ r absorb indices of large valuation), so the reduction in §0 is not even needed. With the first congruence (proved earlier), Bala's conjecture on A376462 is proved in full for all primes p ≥ 5. ∎

## 8. Remarks on the literature (what was adapted, what had to be repaired)

1. Architecture. The proof is Beukers' 1985 proof of a_{mp^r−1} ≡ a_{mp^{r−1}−1} for the ζ(2) Apéry numbers Σ C(n,k)²C(n+k,k) (his Theorem 1, second half), where the unscaled terms also carry only one explicit factor p^r, transplanted to a two-index sum. New here: the two-index block induction with carry labels (Lemma 3.2) and the carry-restricted harmonic sums (Lemma 2.7), the moment kernels and harmonically weighted kernels (Lemma 3.4(c),(d)) that absorb the index coupling in the first-order coefficient ρ, and the decoupling in §7 Step 2.
2. Beukers' Lemma 4(i) (= Lemma 2.5) is true, but its printed proof reduces it to "Σ_{n<p^t} n^k Σ′_{λ≤n} 1/λ ≡ 0 (mod p^t) for all k ≥ 0" (the unnumbered display before his (10); (10) itself is the equivalent k!·C(n,k) form, which fails likewise), which is false already for k = 0: Σ_{n<p^t} H′_n = p^tH′_{p^t−1} − (p^t − p^{t−1}) ≡ p^{t−1} (mod p^t) (e.g. Σ_{n<5}H′_n = 77/12 ≡ 1 mod 5). The Abel-summation step there drops the restriction p ∤ (n+1). The lemma holds because the j = 0 and j = 1 terms of the expansion of σ_s(n) cancel; the reflection proof given above avoids the expansion altogether.
3. Beukers states Lemma 4(ii) modulo p^{t+s}; his proof (and ours, Lemma 2.6) gives p^{t+2s}. His printed proof treats only the block i = 0 (k = 1, …, p^t − 1) although the statement is for every block; the general block is proved here (Lemma 2.6). The stronger form is what the stratified argument on his pp. 153–154 — and our §7 — needs: with only p^{t+s} the count there gives p^{2r−s} instead of p^{2r}.
4. Straub's 2014 route (identity (26) and negative indices) is not available for A376462: the sequence is not in his family and no dual identity of type (26) holds (`numerics/out/a376462_straub_shape_search.txt`, `a376462_dual_identity.txt`), which is why the direct Beukers route was needed.
5. The argument never uses Jacobsthal–Kazandzidis or Bernoulli numbers; all second-order information enters through block sums of 1/k, 1/k² and the two double harmonic lemmas, exactly as in Beukers.

## 9. Numerical confirmation (all exact arithmetic; outputs in `numerics/out/`)

- Theorem for p ∈ {5,7,11}, m ≤ 3, r ≤ 2: `a376462_shift_pattern.txt` (m ≤ 2 also in `a376462_second_structure.txt`); (5,3,1): `a376462_beukers_architecture.txt`; p = 13 at r = 2 and the deep cases up to p = 31 (r = 2), p = 13 (r = 3), p = 7 (r = 4), p = 5 (r = 5): `a376462_deep_direct_test.txt`, `a376462_deep_direct_test2.txt`, `referee_B_wider_primes.txt`; r = 1 for p ≤ 23, m ≤ 6: `rereview_oss_a376462.txt` (§5 block).
- Independent re-check (2026-10-15, code written from the note's definitions): `rereview_shifted_exact.py` (96,408 exact identities), `rereview_shifted_harmonic.py` (70,708), `rereview_shifted_towers.py` (1,096,792), `rereview_shifted_classKJ.py` (750), `rereview_shifted_classSB.py` (36,456, incl. p = 13 and p | m), `rereview_shifted_literature.py` (185), `rereview_shifted_misc.py`; 0 failures on every lemma and step; minimal slack 0 at every stage (table in `verification/referee-reports/REREVIEW-A376462-shifted--fact-only-agent.txt`). The one failing line reproduced a wrong justification sentence in §5 (Ξ is not symmetric), corrected above.
- Class decomposition and reduced sums (r = 2, 3): `a376462_beukers_architecture.txt` (each class vanishes mod p^{3r}; the first-order models are exact to the needed precision; T0, T1, T_B0, T_S vanish to the needed orders).
- The induction of §4 piece by piece (A_s, X_{s,1}, X_{s,2}, X_{s,3}, Y_s by carry, X̂, the top reduction): `a376462_lemma5_dissection.txt`; class J likewise: `a376462_classJ_dissection.txt`. Every piece has slack ≥ 0, often exactly 0 (the bounds are tight).
- Lemma bank: towers with signs, moment kernels, Lemma 2.7(Y),(B), Lemma 2.5 on general blocks: `a376462_lemma_bank_checks.txt`; Lemma 2.6 strong form: `lemma4ii_strength.txt`; §7 decoupling, Lemma 2.1, the reflection identity, and the failure of Beukers' (10): `a376462_final_lemma_checks.txt`; class-S strata: `a376462_classS_strata.txt`.

## 10. References
- P. Bala, OEIS A376462 (2024).
- F. Beukers, Some congruences for the Apéry numbers, J. Number Theory 21 (1985) 141–155 (digest `literature/beukers1985-shifted-method.md`).
- A. Straub, Multivariate Apéry numbers and supercongruences of rational functions, Algebra & Number Theory 8 (2014), arXiv:1401.0854.
- R. Osburn, B. Sahu, A. Straub, Supercongruences for sporadic sequences, Proc. Edinb. Math. Soc. 59 (2016), arXiv:1312.2195.
- `proofs/A376462-first-congruence.md` (first congruence; r = 1 of the second; representation of a(n)).
