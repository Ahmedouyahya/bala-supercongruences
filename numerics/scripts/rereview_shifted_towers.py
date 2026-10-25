"""Re-review of notes/A376462-shifted-congruence-proof.md, part (b), sections 1,3,5,7:
the congruences Lemma 1.2(a),(b); the towers of Lemma 3.4(a)-(d); the
congruence of Lemma 3.5; section 5 (i),(ii),(iii); the towers of section 7
(G_1, G_2, R, R^, and the T_2 analogues) and the Step-3 reductions.

All exact (integers / Fractions); slack recorded.

Output: numerics/out/rereview_shifted_towers.txt
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import (vp, gbinom, Harm, Psi, Xi, Xihat, Phi, Xihat_prime,
                                     K_kernel, K_moment, Kprime_kernel, INF, Tally)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_towers.txt")


def G1(m, u, x, p):
    L = m * p ** u
    return sum(gbinom(L - 1, x + j) ** 2 * gbinom(L + j - 1, j) for j in range(0, max(0, L - x)))


def G2(m, u, y, p):
    L = m * p ** u
    return sum(gbinom(L - 1, k) ** 2 * gbinom(L + k - 1, k) * gbinom(L - 1, k + y) ** 2 for k in range(0, max(0, L - y)))


def R(m, u, kappa, p):
    L = m * p ** u
    return gbinom(L - 1, kappa) ** 2 * (-1) ** (kappa - 1) * gbinom(-L - 1, kappa - 1) * G1(m, u, kappa, p)


def Rhat(m, w, q, p):
    L = m * p ** w
    return gbinom(L - 1, q) ** 2 * (-1) ** q * gbinom(-L - 1, q) * G1(m, w, q, p)


def R2(m, u, iota, p):
    L = m * p ** u
    return (-1) ** (iota - 1) * gbinom(-L - 1, iota - 1) * G2(m, u, iota, p)


def R2hat(m, w, q, p):
    L = m * p ** w
    return (-1) ** q * gbinom(-L - 1, q) * G2(m, w, q, p)


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (b): towers and kernel congruences (sections 1, 3, 5, 7)")

        # ---------------------------------------------------- Lemma 1.2
        T.log("Lemma 1.2 (a),(b) for positive and negative m")
        for p in (5, 7):
            for m in (-5, -2, -1, 1, 2, 3, 5):
                for s in (1, 2, 3):
                    L, Lp = m * p ** s, m * p ** (s - 1)
                    top = min(abs(L) + p + 2, 400)
                    for n in range(0, top):
                        d = (-1) ** n * gbinom(L - 1, n) - (-1) ** (n // p) * gbinom(Lp - 1, n // p)
                        T.val("L1.2(a) mod p^s", d, s, p, f"p={p} m={m} s={s} n={n}")
                        if n % p == 0:
                            d = gbinom(L, n) - gbinom(Lp, n // p)
                            T.val("L1.2(b) mod p^s", d, s, p, f"p={p} m={m} s={s} n={n}")
                        else:
                            d = (-1) ** (n - 1) * gbinom(L - 1, n - 1) - (-1) ** (n // p) * gbinom(Lp - 1, n // p)
                            T.val("L1.2 consequence (n-1 shift, p∤n) mod p^s", d, s, p, f"p={p} m={m} s={s} n={n}")
                        T.val("L1.2 squares C(L-1,n)^2 mod p^s", gbinom(L - 1, n) ** 2 - gbinom(Lp - 1, n // p) ** 2, s, p, f"p={p} m={m} s={s} n={n}")

        # ---------------------------------------------------- Lemma 3.4 and 3.5
        T.log("Lemma 3.4 (a)-(d), Lemma 3.5 congruence, (4.a) tower K^_r -> K_{r-1}")
        for p in (5, 7):
            Hm = Harm(p)
            for m in (1, 2, 5):
                for u in (1, 2, 3):
                    L, Lp = m * p ** u, m * p ** (u - 1)
                    if L > 350:
                        continue
                    for q in range(0, L + 2):
                        qp = q // p
                        # (a) unscaled
                        for j in range(0, L + 2 - q):
                            if j % p:
                                T.val("L3.4(a) unscaled Psi_u(q,j) = 0 mod p^u", Psi(L, q, j), u, p, f"p={p} m={m} u={u} q={q} j={j}")
                            else:
                                T.val("L3.4(a) scaled Psi_u(q,pj1) = Psi_{u-1}(q',j1) mod p^u", Psi(L, q, j) - Psi(Lp, qp, j // p), u, p, f"p={p} m={m} u={u} q={q} j={j}")
                        # (a) K tower
                        T.val("L3.4(a) K_u(q) = K_{u-1}(q') mod p^u", K_kernel(L, q) - K_kernel(Lp, qp), u, p, f"p={p} m={m} u={u} q={q}")
                        # (c) moment kernels
                        for t in (1, 2, 3):
                            T.val(f"L3.4(c) K_u^[t] = 0 mod p^u (t={t})", K_moment(L, q, t), u, p, f"p={p} m={m} u={u} q={q}")
                        # (d) harmonically weighted kernels
                        for d in (1, 2):
                            lhs = sum(Psi(L, q, j) * Hm.H(p ** d * j) for j in range(0, max(0, L - q)))
                            rhs = sum(Psi(Lp, qp, j1) * Hm.H(p ** (d + 1) * j1) for j1 in range(0, max(0, Lp - qp)))
                            T.val(f"L3.4(d) Ktilde_u^(d) = Ktilde_(u-1)^(d+1) mod p^u (d={d})", lhs - rhs, u, p, f"p={p} m={m} u={u} q={q}")
                        # (4.a) K^_r(k) = sum_{j1} Psi_r(k,p j1) ≡ K_{r-1}([k/p]) mod p^r
                        Khat = sum(Psi(L, q, p * j1) for j1 in range(0, Lp + 1))
                        T.val("(4.a) K^_r(k) = K_{r-1}([k/p]) mod p^r", Khat - K_kernel(Lp, qp), u, p, f"p={p} m={m} r={u} k={q}")
                        # (b) Xi tower
                        if q <= L:
                            for qq in range(0, L + 1 - q):
                                for delta in (0, 1):
                                    dp = int((q % p) + (qq % p) + delta >= p)
                                    T.val("L3.4(b) Xi_u^(d) = Xi_(u-1)^(d') mod p^u", Xi(L, delta, q, qq) - Xi(Lp, dp, qp, qq // p), u, p, f"p={p} m={m} u={u} q={q} q'={qq} delta={delta}")
                                if qq % p and qq >= 1:
                                    dl = int((q % p) + (qq % p) >= p)
                                    T.val("L3.4(b) Xi^_u(n,j) = Xi_(u-1)^(delta)([n/p],[j/p]) mod p^u", Xihat(L, q, qq) - Xi(Lp, dl, qp, qq // p), u, p, f"p={p} m={m} u={u} n={q} j={qq}")
                    # Lemma 3.5 congruence (u here plays the role of u+1 in the lemma)
                    for n in range(0, L + 1):
                        for j1 in range(0, Lp + 1):
                            rho = Hm.H(n) - Hm.H(p * j1) + 2 * Hm.H(n + p * j1)
                            d = Psi(L, n, p * j1) - Psi(Lp, n // p, j1) * (1 - L * rho)
                            T.val("L3.5 congruence mod p^{2u+2}", d, 2 * u, p, f"p={p} m={m} u+1={u} n={n} j1={j1}")

        # ---------------------------------------------------- section 5
        T.log("Section 5: (i) Xi^' tower, (ii) rho' congruence, (iii) K', moment and harmonic kernels for Phi, (iv) K^'_r tower")
        for p in (5, 7):
            Hm = Harm(p)
            for m in (1, 2, 5):
                for u in (1, 2, 3):
                    L, Lp = m * p ** u, m * p ** (u - 1)
                    if L > 350:
                        continue
                    for j in range(0, L + 2):
                        jp = j // p
                        # (i): p∤k
                        for k in range(1, L + 1 - j):
                            if k % p:
                                dl = int((k % p) + (j % p) >= p)
                                T.val("sec5(i) Xi^'_u(k,j) = Xi_(u-1)^(delta)([k/p],[j/p]) mod p^u", Xihat_prime(L, k, j) - Xi(Lp, dl, k // p, jp), u, p, f"p={p} m={m} u={u} k={k} j={j}")
                                T.check("sec5(i) Phi = (L/k) Xi^'", Fraction(Phi(L, k, j)) == Fraction(L, k) * Xihat_prime(L, k, j), f"p={p} m={m} u={u} k={k} j={j}")
                                T.val("sec5 unscaled Phi_u(k,j) = 0 mod p^u", Phi(L, k, j), u, p, f"p={p} m={m} u={u} k={k} j={j}")
                            else:
                                T.val("sec5 scaled Phi_u(pk1,j) = Phi_{u-1}(k1,[j/p]) mod p^u", Phi(L, k, j) - Phi(Lp, k // p, jp), u, p, f"p={p} m={m} u={u} k={k} j={j}")
                        # (iii) K' tower, moments, harmonic
                        T.val("sec5(iii) K'_u(j) = K'_{u-1}([j/p]) mod p^u", Kprime_kernel(L, j) - Kprime_kernel(Lp, jp), u, p, f"p={p} m={m} u={u} j={j}")
                        for t in (1, 2):
                            T.val(f"sec5(iii) sum_k k^t Phi_u(k,j) = 0 mod p^u (t={t})", sum(k ** t * Phi(L, k, j) for k in range(0, max(0, L - j))), u, p, f"p={p} m={m} u={u} j={j}")
                        for d in (1, 2):
                            lhs = sum(Phi(L, k, j) * Hm.H(p ** d * k) for k in range(0, max(0, L - j)))
                            rhs = sum(Phi(Lp, k1, jp) * Hm.H(p ** (d + 1) * k1) for k1 in range(0, max(0, Lp - jp)))
                            T.val(f"sec5(iii) harmonic kernel tower for Phi mod p^u (d={d})", lhs - rhs, u, p, f"p={p} m={m} u={u} j={j}")
                        Khatp = sum(Phi(L, p * k1, j) for k1 in range(0, Lp + 1))
                        T.val("sec5(iv) K^'_r(j) = K'_{r-1}([j/p]) mod p^r", Khatp - Kprime_kernel(Lp, jp), u, p, f"p={p} m={m} r={u} j={j}")
                    # (ii)
                    for k1 in range(0, Lp + 1):
                        for j in range(0, L + 1):
                            rhop = -Hm.H(j) + Hm.H(p * k1) + 2 * Hm.H(j + p * k1)
                            d = Phi(L, p * k1, j) - Phi(Lp, k1, j // p) * (1 - L * rhop)
                            T.val("sec5(ii) congruence mod p^{2u+2}", d, 2 * u, p, f"p={p} m={m} u+1={u} k1={k1} j={j}")

        # ---------------------------------------------------- section 7 towers
        T.log("Section 7: towers G_1, G_2, R -> R^, R^ tower; T_2 analogues; Step-3 reductions")
        for p in (5, 7):
            for m in (1, 2, 5):
                for u in (1, 2, 3):
                    L, Lp = m * p ** u, m * p ** (u - 1)
                    if L > 350:
                        continue
                    for x in range(0, L + 2):
                        T.val("sec7 G_1 tower mod p^u", G1(m, u, x, p) - G1(m, u - 1, x // p, p), u, p, f"p={p} m={m} u={u} x={x}")
                        T.val("sec7 G_2 tower mod p^u", G2(m, u, x, p) - G2(m, u - 1, x // p, p), u, p, f"p={p} m={m} u={u} y={x}")
                        T.val("sec7 R^ tower mod p^w", Rhat(m, u, x, p) - Rhat(m, u - 1, x // p, p), u, p, f"p={p} m={m} w={u} q={x}")
                        T.val("sec7 R2^ tower mod p^w", R2hat(m, u, x, p) - R2hat(m, u - 1, x // p, p), u, p, f"p={p} m={m} w={u} q={x}")
                        if x % p and x >= 1:
                            T.val("sec7 R^(u)(kappa) = R^^(u-1)([kappa/p]) mod p^u (p∤kappa)", R(m, u, x, p) - Rhat(m, u - 1, x // p, p), u, p, f"p={p} m={m} u={u} kappa={x}")
                            T.val("sec7 R2^(u)(iota) = R2^^(u-1)([iota/p]) mod p^u (p∤iota)", R2(m, u, x, p) - R2hat(m, u - 1, x // p, p), u, p, f"p={p} m={m} u={u} iota={x}")
            # Step 3 reductions: sigma-1 steps from level r-1 down to r-sigma, modulus p^{r-sigma+1}
            for (m, r) in ((1, 2), (2, 2), (1, 3), (2, 3)):
                M = m * p ** (r - 1)
                if M > 100:
                    continue
                for kp in range(1, M):
                    sig = vp(p * kp, p)
                    if sig > r - 1:
                        continue
                    kappa = kp // p ** (sig - 1)
                    mod = r - sig + 1
                    T.val("Step3 C(M-1,k')^2 -> C(mp^{r-s}-1,kappa)^2 mod p^{r-s+1}", gbinom(M - 1, kp) ** 2 - gbinom(m * p ** (r - sig) - 1, kappa) ** 2, mod, p, f"p={p} m={m} r={r} k'={kp}")
                    T.val("Step3 (-1)^{k'-1}C(-M-1,k'-1) -> (-1)^{kappa-1}C(-mp^{r-s}-1,kappa-1) mod p^{r-s+1}",
                          (-1) ** (kp - 1) * gbinom(-M - 1, kp - 1) - (-1) ** (kappa - 1) * gbinom(-m * p ** (r - sig) - 1, kappa - 1), mod, p, f"p={p} m={m} r={r} k'={kp}")
                    T.val("Step3 G_1(k') -> G_1^(r-s)(kappa) mod p^{r-s+1}", G1(m, r - 1, kp, p) - G1(m, r - sig, kappa, p), mod, p, f"p={p} m={m} r={r} k'={kp}")
                    T.val("Step4 G_2(j') -> G_2^(r-s)(iota) mod p^{r-s+1}", G2(m, r - 1, kp, p) - G2(m, r - sig, kappa, p), mod, p, f"p={p} m={m} r={r} j'={kp}")

        T.summary("rereview_shifted_towers")


if __name__ == "__main__":
    main()
