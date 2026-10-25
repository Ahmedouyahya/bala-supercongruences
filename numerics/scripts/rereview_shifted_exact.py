"""Re-review of notes/A376462-shifted-congruence-proof.md, part (a):
EXACT identities, tested with Fractions, including edge cases.

Items: Lemma 1.1 (i),(ii) for positive and negative m; Lemma 1.3 (e_1, e_2,
integrality of all e_d); Lemma 3.3; Lemma 3.5 exact model; section 5 (ii)
exact model for Phi; class decomposition S+K+J+B = a(N-1); the exact
expansions in the proofs of Lemma 2.3, 2.5 (alpha),(beta), 2.6; section 4
(4.1) algebra; section 6 algebra; section 7 E-identity, Step 2 identity and
Z-integrality; the series in X^_3; Step 3 factor identity.

Output: numerics/out/rereview_shifted_exact.txt
"""
import os
import sys
import random
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import (vp, gbinom, Harm, Stilde, a_seq, Psi, Xi, Xihat,
                                     Phi, Xihat_prime, INF, Tally)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_exact.txt")
random.seed(20261015)


def poly_mul(a, b):
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def expand_E(p, factors):
    """factors: list of (x, kind, mult) with kind '+' for Pbar_x, '-' for P_x.
    Returns coefficient list e_d of E = prod as polynomial in L (exact)."""
    poly = [Fraction(1)]
    for x, kind, mult in factors:
        for lam in range(1, x + 1):
            if lam % p == 0:
                continue
            f = [Fraction(1), Fraction(-1 if kind == '-' else 1, lam)]
            for _ in range(mult):
                poly = poly_mul(poly, f)
    return poly


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (a): exact identities of the shifted-congruence note")
        T.log("")

        # ---------------------------------------------------- Lemma 1.1
        T.log("Lemma 1.1 (i),(ii): any integer m (negative included), s=1,2")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for m in (-5, -3, -2, -1, 1, 2, 3, 5, 7):
                for s in (1, 2):
                    L, Lp = m * p ** s, m * p ** (s - 1)
                    for n in range(0, 2 * p * p + 3):
                        q = n // p
                        prod1 = Fraction(1)
                        for lam in range(1, n + 1):
                            if lam % p:
                                prod1 *= Fraction(L - lam, lam)
                        lhs = gbinom(L - 1, n)
                        rhs1 = gbinom(Lp - 1, q) * prod1
                        rhs2 = (-1) ** (n - q) * gbinom(Lp - 1, q) * Hm.P(n, L)
                        T.check("L1.1(i) first form", lhs == rhs1, f"p={p} m={m} s={s} n={n}")
                        T.check("L1.1(i) second form", lhs == rhs2, f"p={p} m={m} s={s} n={n}")
                        cnt += 2
                        if n % p == 0:
                            lhs = gbinom(L, n)
                            rhs1 = gbinom(Lp, n // p) * prod1
                            rhs2 = gbinom(Lp, n // p) * Hm.P(n, L)
                            T.check("L1.1(ii) first form", lhs == rhs1, f"p={p} m={m} s={s} n={n}")
                            T.check("L1.1(ii) second form", lhs == rhs2, f"p={p} m={m} s={s} n={n}")
                            cnt += 2
        T.log(f"  {cnt} identities tested")

        # ---------------------------------------------------- Lemma 1.3
        T.log("Lemma 1.3: e_1, e_2 formulas and integrality of every e_d")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for trial in range(40):
                nf = random.randint(1, 4)
                factors = []
                for _ in range(nf):
                    x = random.randint(0, 3 * p + 2)
                    kind = random.choice('+-')
                    mult = random.randint(0, 3)
                    factors.append((x, kind, mult))
                coeffs = expand_E(p, factors)
                e1 = sum((-mult if kind == '-' else mult) * Hm.H(x) for x, kind, mult in factors)
                e2 = Fraction(1, 2) * e1 * e1 - Fraction(1, 2) * sum(mult * Hm.S2(x) for x, kind, mult in factors)
                got1 = coeffs[1] if len(coeffs) > 1 else Fraction(0)
                got2 = coeffs[2] if len(coeffs) > 2 else Fraction(0)
                T.check("L1.3 e_0 = 1", coeffs[0] == 1, str(factors))
                T.check("L1.3 e_1 formula", got1 == e1, f"p={p} {factors}")
                T.check("L1.3 e_2 formula", got2 == e2, f"p={p} {factors}")
                for d, c in enumerate(coeffs):
                    T.check("L1.3 e_d integral", vp(c, p) >= 0, f"p={p} d={d} {factors}")
                # the valuation bound on e_2
                bound = min([2 * vp(e1, p)] + [vp(Hm.S2(x), p) for x, kind, mult in factors if mult > 0] or [0])
                T.check("L1.3 v(e_2) >= min(2v(e_1), v(S_2))", vp(got2, p) >= min(bound, INF), f"p={p} {factors}")
                cnt += 1
        T.log(f"  {cnt} random products tested")

        # ---------------------------------------------------- Lemma 3.3
        T.log("Lemma 3.3: S~(N;k,j) = (N/(N+k)) Psi_r(k,j); Psi_u(n,j) = (L_u/j) Xi^_u(n,j)")
        cnt = 0
        for p in (5, 7):
            for (m, r) in ((1, 1), (2, 1), (1, 2), (3, 1), (p, 1)):
                N = m * p ** r
                for k in range(0, N + 2):
                    for j in range(0, N + 2 - k):
                        lhs = Fraction(Stilde(N, k, j))
                        rhs = Fraction(N, N + k) * Psi(N, k, j)
                        T.check("L3.3 S~ = N/(N+k) Psi", lhs == rhs, f"p={p} N={N} k={k} j={j}")
                        cnt += 1
                        if j >= 1:
                            T.check("L3.3 Psi = (L/j) Xi^", Fraction(Psi(N, k, j)) == Fraction(N, j) * Xihat(N, k, j),
                                    f"p={p} N={N} k={k} j={j}")
                            cnt += 1
        T.log(f"  {cnt} identities tested")

        # ---------------------------------------------------- Lemma 3.5 exact and sec 5(ii)
        T.log("Lemma 3.5 exact: Psi_{u+1}(n,p j1) = Psi_u([n/p],j1) P_n^2 Pbar_n P_{n+pj1}^2 Pbar_{pj1}")
        T.log("Section 5(ii) exact: Phi_{u+1}(p k1,j) = Phi_u(k1,[j/p]) Pbar_{pk1} P_{pk1}^2 P_{pk1+j}^2 Pbar_j")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for m in (1, 2, 5):
                for u in (0, 1, 2):
                    L = m * p ** (u + 1)
                    Lp = m * p ** u
                    if L > 260:
                        continue
                    for n in range(0, L + 3):
                        P_n2 = Hm.P(n, L) ** 2
                        Pb_n = Hm.Pbar(n, L)
                        for j1 in range(0, Lp + 2):
                            lhs = Fraction(Psi(L, n, p * j1))
                            rhs = Psi(Lp, n // p, j1) * P_n2 * Pb_n * Hm.P(n + p * j1, L) ** 2 * Hm.Pbar(p * j1, L)
                            T.check("L3.5 exact model", lhs == rhs, f"p={p} m={m} u={u} n={n} j1={j1}")
                            cnt += 1
                    for k1 in range(0, Lp + 2):
                        for j in range(0, L + 3):
                            lhs = Fraction(Phi(L, p * k1, j))
                            rhs = (Phi(Lp, k1, j // p) * Hm.Pbar(p * k1, L) * Hm.P(p * k1, L) ** 2
                                   * Hm.P(p * k1 + j, L) ** 2 * Hm.Pbar(j, L))
                            T.check("sec5(ii) exact model for Phi", lhs == rhs, f"p={p} m={m} u={u} k1={k1} j={j}")
                            cnt += 1
        T.log(f"  {cnt} identities tested")

        # ---------------------------------------------------- Lemma 3.5 first-order coefficient
        T.log("Lemma 3.5 / sec 5(ii): first-order coefficients rho, rho' (E - 1 + L rho) / L^2 integral")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for m in (1, 2):
                for u in (0, 1):
                    L = m * p ** (u + 1)
                    for n in range(0, L + 1):
                        for j1 in range(0, m * p ** u + 1):
                            E = Hm.P(n, L) ** 2 * Hm.Pbar(n, L) * Hm.P(n + p * j1, L) ** 2 * Hm.Pbar(p * j1, L)
                            rho = Hm.H(n) - Hm.H(p * j1) + 2 * Hm.H(n + p * j1)
                            T.check("L3.5 rho: (E-1+L rho)/L^2 integral", vp((E - 1 + L * rho) / (L * L), p) >= 0,
                                    f"p={p} m={m} u={u} n={n} j1={j1}")
                            cnt += 1
                    for k1 in range(0, m * p ** u + 1):
                        for j in range(0, L + 1):
                            E = Hm.Pbar(p * k1, L) * Hm.P(p * k1, L) ** 2 * Hm.P(p * k1 + j, L) ** 2 * Hm.Pbar(j, L)
                            rhop = -Hm.H(j) + Hm.H(p * k1) + 2 * Hm.H(j + p * k1)
                            T.check("sec5 rho': (E-1+L rho')/L^2 integral", vp((E - 1 + L * rhop) / (L * L), p) >= 0,
                                    f"p={p} m={m} u={u} k1={k1} j={j}")
                            cnt += 1
        T.log(f"  {cnt} identities tested")

        # ---------------------------------------------------- class decomposition
        T.log("Class decomposition: Sigma_S + Sigma_K + Sigma_J + Sigma_B = a(N-1)")
        for p in (5, 7, 11):
            for (m, r) in ((1, 1), (2, 1), (1, 2), (p, 1)):
                N = m * p ** r
                if N > 130:
                    continue
                tot = {"S": 0, "K": 0, "J": 0, "B": 0}
                for k in range(0, N):
                    for j in range(0, N - k):
                        cls = ("S" if (k % p == 0 and j % p == 0) else "K" if (k % p and j % p == 0)
                               else "J" if (k % p == 0 and j % p) else "B")
                        tot[cls] += Stilde(N, k, j)
                T.check("class decomposition sums to a(N-1)", sum(tot.values()) == a_seq(N - 1), f"p={p} N={N}")
        T.log("  done")

        # ---------------------------------------------------- Lemma 2.3 exact expansions
        T.log("Lemma 2.3 proof: exact expansions with integral remainders")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for t in (1, 2):
                pt = p ** t
                for n in range(0, pt):
                    tail2 = sum((Fraction(1, mu * mu) for mu in range(n + 1, pt) if mu % p), Fraction(0))
                    rem = Hm.H(pt - 1 - n) + (Hm.H(pt - 1) - Hm.H(n)) + pt * tail2
                    T.check("L2.3 first: remainder /p^{2t} integral", vp(rem / pt ** 2, p) >= 0, f"p={p} t={t} n={n}")
                    cnt += 1
                for s in (1, 2):
                    pts = p ** (t + s)
                    for k in range(0, pt + 1):
                        tail2 = sum((Fraction(1, mu * mu) for mu in range(k * p ** s + 1, pts) if mu % p), Fraction(0))
                        rem = Hm.H((pt - k) * p ** s) + (Hm.H(pts) - Hm.H(k * p ** s)) + pts * tail2
                        T.check("L2.3 second: remainder /p^{2(t+s)} integral", vp(rem / pts ** 2, p) >= 0,
                                f"p={p} t={t} s={s} k={k}")
                        # the middle sum runs over full p^s blocks: check
                        T.check("L2.3 second: tail sum over full p^s-blocks = 0 mod p^s", vp(tail2, p) >= s,
                                f"p={p} t={t} s={s} k={k}")
                        cnt += 2
        T.log(f"  {cnt} checks")

        # ---------------------------------------------------- Lemma 2.5 (alpha),(beta)
        T.log("Lemma 2.5 proof: (alpha),(beta) exact with integral eta, theta; tau_s = 0 mod p^s")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for t in (1, 2):
                pt = p ** t
                for i in (1, 2, 3, p, p + 1):
                    for nbar in range(0, pt):
                        n = i * pt + nbar
                        eta = (Hm.H(n) - Hm.H(i * pt) - Hm.H(nbar) + i * pt * Hm.S2(nbar)) / pt ** 2
                        T.check("L2.5 (alpha) eta integral", vp(eta, p) >= 0, f"p={p} t={t} i={i} nbar={nbar}")
                        # explicit eta from the note: i^2 sum' 1/(lam^2 (i p^t + lam))
                        eta_note = sum((Fraction(i * i, lam * lam * (i * pt + lam)) for lam in range(1, nbar + 1) if lam % p), Fraction(0))
                        T.check("L2.5 (alpha) eta matches explicit", eta == eta_note, f"p={p} t={t} i={i} nbar={nbar}")
                        cnt += 2
                        for s in (0, 1, 2):
                            tp = t + s
                            tau = Hm.block_S2(s, nbar)
                            theta = (Hm.sigma(s, n) - Hm.sigma(s, nbar) + i * p ** tp * tau) / p ** (2 * tp)
                            T.check("L2.5 (beta) theta integral", vp(theta, p) >= 0, f"p={p} t={t} s={s} i={i} nbar={nbar}")
                            T.check("L2.5 (beta) tau_s = 0 mod p^s", vp(tau, p) >= s, f"p={p} t={t} s={s} i={i} nbar={nbar}")
                            cnt += 2
        T.log(f"  {cnt} checks")

        # ---------------------------------------------------- Lemma 2.6 general block expansion
        T.log("Lemma 2.6 proof: H'_{kp^s} = H'_{ip^{t+s}} + H'_{kbar p^s} - i p^{t+s} S_2(kbar p^s) + p^{2(t+s)} (integral)")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for t in (1, 2):
                for s in (1, 2):
                    if p ** (t + s) * 3 > 3000:
                        continue
                    for i in (1, 2):
                        for kbar in range(1, p ** t):
                            if kbar % p == 0:
                                continue
                            k = i * p ** t + kbar
                            rem = Hm.H(k * p ** s) - Hm.H(i * p ** (t + s)) - Hm.H(kbar * p ** s) + i * p ** (t + s) * Hm.S2(kbar * p ** s)
                            T.check("L2.6 expansion remainder integral", vp(rem / p ** (2 * (t + s)), p) >= 0,
                                    f"p={p} t={t} s={s} i={i} kbar={kbar}")
                            T.check("L2.6 1/k expansion remainder integral",
                                    vp((Fraction(1, k) - Fraction(1, kbar) + Fraction(i * p ** t, kbar * kbar)) / p ** (2 * t), p) >= 0,
                                    f"p={p} t={t} i={i} kbar={kbar}")
                            cnt += 2
        T.log(f"  {cnt} checks")

        # ---------------------------------------------------- sigma additivity
        T.log("sigma additivity: sum_{n in B_u(l)} sigma_t(n) = sigma_{t+u}(l)")
        for p in (5, 7):
            Hm = Harm(p)
            for t in (0, 1, 2):
                for u in (0, 1, 2):
                    for l in (0, 1, 2):
                        if p ** (t + u) * (l + 1) > 5000:
                            continue
                        lhs = sum(Hm.sigma(t, n) for n in range(l * p ** u, (l + 1) * p ** u))
                        T.check("sigma additivity", lhs == Hm.sigma(t + u, l), f"p={p} t={t} u={u} l={l}")
        T.log("  done")

        # ---------------------------------------------------- section 4 (4.1) algebra, section 6 algebra
        T.log("Section 4 (4.1) and section 6 algebra")
        for p in (5, 7):
            for (m, r) in ((1, 1), (1, 2), (2, 1)):
                N = m * p ** r
                for k in range(1, N):
                    if k % p == 0:
                        continue
                    lhs = Fraction(N, N + k)
                    rhs = Fraction(N, k) - Fraction(N * N, k * k) + Fraction(N ** 3, k ** 3) / (1 + Fraction(N, k))
                    T.check("(4.1) algebra N/(N+k)", lhs == rhs, f"p={p} N={N} k={k}")
                    T.check("(4.1) last term in p^{3r}", vp(Fraction(N ** 3, k ** 3) / (1 + Fraction(N, k)), p) >= 3 * r, f"p={p} N={N} k={k}")
                    for j in range(1, N - k):
                        if j % p == 0:
                            continue
                        lhs = Fraction(Stilde(N, k, j))
                        rhs = Fraction(N * N, k * j) * Xihat(N, k, j) - Fraction(N ** 3, k * k * j) / (1 + Fraction(N, k)) * Xihat(N, k, j)
                        T.check("sec6 S~ = N^2/(kj) Xi^ - ...", lhs == rhs, f"p={p} N={N} k={k} j={j}")
        T.log("  done")

        # ---------------------------------------------------- section 7 E-identity, Step 2
        T.log("Section 7: S~(N;pk',pj') = S~(M;k',j') E ; Step 2 identity ; Z integral, v(Z) >= 1+b")
        cnt = 0
        for p in (5, 7):
            Hm = Harm(p)
            for (m, r) in ((1, 1), (2, 1), (1, 2), (p, 1), (2, 2)):
                N, M = m * p ** r, m * p ** (r - 1)
                if N > 260:
                    continue
                for kp in range(0, M):
                    for jp in range(0, M - kp):
                        E = Hm.P(p * kp, N) ** 2 * Hm.Pbar(p * kp, N) * Hm.P(p * (kp + jp), N) ** 2 * Hm.Pbar(p * jp, N)
                        T.check("sec7 E-identity", Fraction(Stilde(N, p * kp, p * jp)) == Stilde(M, kp, jp) * E,
                                f"p={p} N={N} k'={kp} j'={jp}")
                        rhoS = Hm.H(p * kp) + 2 * Hm.H(p * (kp + jp)) - Hm.H(p * jp)
                        T.check("sec7 Step1 (E-1+N rho_S)/N^2 integral", vp((E - 1 + N * rhoS) / (N * N), p) >= 0,
                                f"p={p} N={N} k'={kp} j'={jp}")
                        cnt += 2
                        if jp >= 1:
                            Z = sum((Fraction(1, mu * (mu + p * kp)) for mu in range(1, p * jp + 1) if mu % p), Fraction(0))
                            T.check("sec7 Step2 identity", Hm.H(p * (kp + jp)) - Hm.H(p * kp) == Hm.H(p * jp) - p * kp * Z,
                                    f"p={p} N={N} k'={kp} j'={jp}")
                            b = vp(jp, p)
                            T.val("sec7 Step2 v(Z) >= 1+b", Z, 1 + b, p, f"p={p} N={N} k'={kp} j'={jp}")
                            T.check("sec7 Step2 rho_S = 3H'_{pk'} + H'_{pj'} - 2pk'Z",
                                    rhoS == 3 * Hm.H(p * kp) + Hm.H(p * jp) - 2 * p * kp * Z, f"p={p} k'={kp} j'={jp}")
                            cnt += 3
        T.log(f"  {cnt} checks")

        # ---------------------------------------------------- X^_3 series identity
        T.log("X^_3 expansion: H'_{k+pj1} - H'_{pj1} = sum_t (-p)^t j1^t S_{t+1}(k); truncation error valuation")
        for p in (5, 7):
            Hm = Harm(p)
            for j1 in (0, 1, 2, p, 2 * p + 1):
                for k in range(1, 3 * p):
                    if k % p == 0:
                        continue
                    exact = Hm.H(k + p * j1) - Hm.H(p * j1)
                    partial = Fraction(0)
                    for t in range(0, 8):
                        partial += (-p) ** t * j1 ** t * Hm.Sd(t + 1, k)
                        T.check("X^3 series truncation error >= p^{t+1}", vp(exact - partial, p) >= t + 1, f"p={p} j1={j1} k={k} t={t}")
        T.log("  done")

        # ---------------------------------------------------- Step 3 factor identity
        T.log("Section 7 Step 3: C(M+k'-1,k') = (m p^{r-sigma}/kappa) (-1)^{k'-1} C(-M-1,k'-1)")
        for p in (5, 7):
            for (m, r) in ((1, 2), (2, 2), (1, 3)):
                M = m * p ** (r - 1)
                for kp in range(1, M):
                    sig = vp(p * kp, p)
                    kappa = kp // p ** (sig - 1)
                    T.check("Step3 factor identity", Fraction(gbinom(M + kp - 1, kp)) == Fraction(m * p ** (r - sig), kappa) * (-1) ** (kp - 1) * gbinom(-M - 1, kp - 1),
                            f"p={p} m={m} r={r} k'={kp}")
        T.log("  done")

        T.summary("rereview_shifted_exact")


if __name__ == "__main__":
    main()
