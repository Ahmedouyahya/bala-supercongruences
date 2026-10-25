#!/usr/bin/env python3
"""
Referee B (independent) check of notes/A376462-shifted-congruence-proof.md, sections 4-7.

Everything is recomputed from the NOTE'S OWN DEFINITIONS (not from the project's scripts),
in exact rational arithmetic, for (p, r, m) in {(5,2,1), (5,2,2), (7,2,1), (5,3,1)}:

  * the four class sums and (S), (K), (J), (B) mod p^{3r};
  * section 4: (4.1), (4.a), (4.2), X^, X^_1, X^_2, X^_3, A_s (s < r), the step pieces
    X_{s,1}, X_{s,2}, X_{s,3}, Y_s, and the step congruence A_{s+1} = A_s - L X_s + L Y_s;
    Lemma 3.5 termwise; the Lemma 2.7(Y) cell hypothesis for the Y_s weights;
  * section 5: the class-J analogue -- the exact product identity for Phi, the first-order
    coefficient rho' (the note's formula versus the one obtained from Lemma 1.3), the top
    decomposition, A'_s, X^', X'_{s,i}, Y'_s;
  * section 6: Sigma_B = N^2 * sum Xi^_r/(kj) and the inner sum mod p^r; Lemma 2.7(B) cells;
  * section 7: Step 1 (Sigma_S - a(M-1) = -N T_S mod p^{3r}), Step 2 (v(Z) >= 1+b and
    T_S = 3 T_1 + T_2 mod p^{2r}), Steps 3/4 (strata of T_1, T_2 by sigma, their reduced forms,
    and the Lemma-3.1 input sums mod p^{r-sigma}).

Run:  ~/venvs/general/bin/python -I numerics/referee_B_shifted_assembly.py
Output is also written to numerics/out/referee_B_shifted_assembly.txt
"""
import os
import sys
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, inf

LINES = []


def out(s=""):
    print(s)
    LINES.append(s)


# ----------------------------------------------------------------------------
# basic arithmetic
# ----------------------------------------------------------------------------
@lru_cache(maxsize=None)
def C(a, b):
    """C(a,b) = a(a-1)...(a-b+1)/b! for b >= 0 (any integer a), 0 for b < 0."""
    if b < 0:
        return 0
    num = 1
    for i in range(b):
        num *= (a - i)
    return num // factorial(b)


def vp(x, p):
    if x == 0:
        return inf
    x = F(x)
    n, d = x.numerator, x.denominator
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v


def fv(v):
    return "inf" if v == inf else str(v)


def check(label, value, p, e, ctx_tag=""):
    """Report v_p(value) against the claimed exponent e; slack = v - e (>= 0 means OK)."""
    v = vp(value, p)
    ok = v >= e
    slack = "inf" if v == inf else str(v - e)
    out(f"  [{'OK ' if ok else 'FAIL'}] {label}: v_p = {fv(v)}, claimed >= {e}, slack {slack}")
    if not ok:
        FAILS.append(f"{label} (v_p = {fv(v)} < {e})")
    return ok


FAILS = []


def must(label, cond):
    out(f"  [{'OK ' if cond else 'FAIL'}] {label}")
    if not cond:
        FAILS.append(label)
    return cond


# ----------------------------------------------------------------------------
# context: one (p, r, m)
# ----------------------------------------------------------------------------
class Ctx:
    def __init__(self, p, r, m):
        self.p, self.r, self.m = p, r, m
        self.N = m * p ** r
        self.M = m * p ** (r - 1)
        self.L = [m * p ** u for u in range(r + 1)]
        # H'_n for n <= p^2 N (the harmonically weighted kernels need H'_{p^2 k})
        H = [F(0)]
        for n in range(1, p * p * self.N + 1):
            H.append(H[-1] + (F(1, n) if n % p else F(0)))
        self.H = H
        self._sig = {}

    # harmonic objects --------------------------------------------------------
    def Hp(self, n):
        return self.H[n]

    def sigma(self, t, n):
        """sigma_t(n) = sum'_{k in B_t(n)} 1/k."""
        key = (t, n)
        if key not in self._sig:
            p = self.p
            lo, hi = n * p ** t, (n + 1) * p ** t
            self._sig[key] = sum((F(1, k) for k in range(max(lo, 1), hi) if k % p), F(0))
        return self._sig[key]

    def S(self, d, x):
        """S_d(x) = sum'_{mu <= x} mu^{-d}."""
        return sum((F(1, mu ** d) for mu in range(1, x + 1) if mu % self.p), F(0))

    def P(self, Lval, x):
        """P_x = prod'_{lambda <= x} (1 - L/lambda)."""
        r = F(1)
        for lam in range(1, x + 1):
            if lam % self.p:
                r *= (1 - F(Lval, lam))
        return r

    def Pbar(self, Lval, x):
        r = F(1)
        for lam in range(1, x + 1):
            if lam % self.p:
                r *= (1 + F(Lval, lam))
        return r

    # kernels (note, section 3) -------------------------------------------------
    def Stilde(self, Nv, k, j):
        return C(Nv - 1, k) ** 2 * C(Nv + k - 1, k) * C(Nv - 1, k + j) ** 2 * C(Nv + j - 1, j)

    def Psi(self, u, n, j):
        L = self.L[u]
        return (C(L - 1, n) ** 2 * (-1) ** n * C(-L - 1, n)
                * C(L - 1, n + j) ** 2 * (-1) ** j * C(-L, j))

    def K(self, u, n):
        L = self.L[u]
        if n >= L:
            return 0
        return sum(self.Psi(u, n, j) for j in range(0, L - n))

    def Khat(self, u, k):
        """K^_u(k) = sum_{j1} Psi_u(k, p j1) (only scaled j)."""
        L = self.L[u]
        if k >= L:
            return 0
        return sum(self.Psi(u, k, self.p * j1) for j1 in range(0, (L - 1 - k) // self.p + 1))

    def Xi(self, u, delta, q, qp):
        L = self.L[u]
        return (C(L - 1, q) ** 2 * (-1) ** q * C(-L - 1, q)
                * C(L - 1, q + qp + delta) ** 2 * (-1) ** qp * C(-L - 1, qp))

    def Xihat(self, u, n, j):
        L = self.L[u]
        return (C(L - 1, n) ** 2 * (-1) ** n * C(-L - 1, n)
                * C(L - 1, n + j) ** 2 * (-1) ** (j - 1) * C(-L - 1, j - 1))

    # class-J kernels (section 5)
    def Phi(self, u, k, j):
        L = self.L[u]
        return (C(L - 1, k) ** 2 * (-1) ** k * C(-L, k)
                * C(L - 1, k + j) ** 2 * (-1) ** j * C(-L - 1, j))

    def Kprime(self, u, j):
        L = self.L[u]
        if j >= L:
            return 0
        return sum(self.Phi(u, k, j) for k in range(0, L - j))

    def Khatprime(self, u, j):
        L = self.L[u]
        if j >= L:
            return 0
        return sum(self.Phi(u, self.p * k1, j) for k1 in range(0, (L - 1 - j) // self.p + 1))

    def Xihatprime(self, u, k, j):
        L = self.L[u]
        return (C(L - 1, k) ** 2 * (-1) ** (k - 1) * C(-L - 1, k - 1)
                * C(L - 1, k + j) ** 2 * (-1) ** j * C(-L - 1, j))


# ----------------------------------------------------------------------------
# section 0: classes
# ----------------------------------------------------------------------------
def class_sums(cx):
    p, N = cx.p, cx.N
    sums = {"S": 0, "K": 0, "J": 0, "B": 0}
    for k in range(N):
        for j in range(N - k):
            t = cx.Stilde(N, k, j)
            if t == 0:
                continue
            cls = ("S" if j % p == 0 else "J") if k % p == 0 else ("K" if j % p == 0 else "B")
            sums[cls] += t
    return sums


def a_of(cx, Nv):
    return sum(cx.Stilde(Nv, k, j) for k in range(Nv) for j in range(Nv - k))


# ----------------------------------------------------------------------------
# section 4: class K
# ----------------------------------------------------------------------------
def section4(cx):
    p, r, m, N, M = cx.p, cx.r, cx.m, cx.N, cx.M
    out("--- Section 4 (class K) ---")
    SigK = sum(cx.Stilde(N, k, j) for k in range(1, N) if k % p
               for j in range(0, N - k, p))
    T1 = sum(F(1, k) * cx.Khat(r, k) for k in range(1, N) if k % p)      # sum' (1/k) K^_r(k)
    T2 = sum(F(1, k * k) * cx.Khat(r, k) for k in range(1, N) if k % p)  # sum' (1/k^2) K^_r(k)
    check("(4.1): Sigma_K - [N*sum'(1/k)K^_r - N^2*sum'(1/k^2)K^_r]", SigK - N * T1 + N * N * T2, p, 3 * r)
    check("(4.a): sum'_{k<N} (1/k^2) K^_r(k)", T2, p, r)
    # tower K^_r -> K_{r-1}
    bad = [k for k in range(1, N) if k % p and vp(cx.Khat(r, k) - cx.K(r - 1, k // p), p) < r]
    must("(4.a) tower: K^_r(k) = K_{r-1}([k/p]) mod p^r for all p-free k < N", not bad)
    # (4.b)
    A = {s: sum(cx.sigma(r - s, n) * cx.K(s, n) for n in range(cx.L[s])) for s in range(r)}
    for s in range(r):
        check(f"A_{s} (claimed mod p^(2r))", A[s], p, 2 * r)

    def rho(u, n, j1):
        return cx.Hp(n) - cx.Hp(p * j1) + 2 * cx.Hp(n + p * j1)

    # Lemma 3.5 termwise at u = r-1 (needed for (4.2)): Psi_r(k,pj1) = Psi_{r-1}(n',j1)(1 - N rho) mod p^{2r}
    worst = inf
    for k in range(N):
        for j1 in range(0, (N - 1 - k) // p + 1):
            lhs = cx.Psi(r, k, p * j1)
            Lw = cx.L[r]
            E = cx.P(Lw, k) ** 2 * cx.Pbar(Lw, k) * cx.P(Lw, k + p * j1) ** 2 * cx.Pbar(Lw, p * j1)
            if lhs != cx.Psi(r - 1, k // p, j1) * E:
                must(f"Lemma 3.5 exact identity fails at (k,j1)=({k},{j1})", False)
            d = lhs - cx.Psi(r - 1, k // p, j1) * (1 - N * rho(r - 1, k, j1))
            worst = min(worst, vp(d, p))
    out(f"  Lemma 3.5 (u=r-1): min v_p(Psi_r(k,pj1) - Psi_(r-1)(n',j1)(1 - N rho)) = {fv(worst)}, claimed >= {2*r}")
    must("Lemma 3.5 congruence at u = r-1", worst >= 2 * r)

    Xhat = sum(F(1, k) * sum(cx.Psi(r - 1, k // p, j1) * rho(r - 1, k, j1)
                             for j1 in range(0, (N - 1 - k) // p + 1))
               for k in range(1, N) if k % p)
    check("(4.2): sum'(1/k)K^_r - (A_{r-1} - N X^)", T1 - (A[r - 1] - N * Xhat), p, 2 * r)
    check("(4.b.1) X^", Xhat, p, r)
    X1 = sum(F(1, k) * cx.Hp(k) * cx.K(r - 1, k // p) for k in range(1, N) if k % p)
    X2 = sum(F(1, k) * sum(cx.Psi(r - 1, k // p, j1) * cx.Hp(p * j1)
                           for j1 in range(0, (N - 1 - k) // p + 1))
             for k in range(1, N) if k % p)
    X3 = sum(F(1, k) * sum(cx.Psi(r - 1, k // p, j1) * cx.Hp(k + p * j1)
                           for j1 in range(0, (N - 1 - k) // p + 1))
             for k in range(1, N) if k % p)
    must("X^ = X^_1 - X^_2 + 2 X^_3 (exact)", Xhat == X1 - X2 + 2 * X3)
    check("X^_1", X1, p, r)
    check("X^_2 (claimed mod p^(r+1))", X2, p, r + 1)
    check("X^_3", X3, p, r)
    check("X^_3 - X^_2 - X^_1 (= the t>=1 tail of the series)", X3 - X2 - X1, p, r)

    # induction step pieces, s = 0..r-2
    for s in range(0, r - 1):
        sp = r - s - 1
        Lv = cx.L[s + 1]
        # termwise model for K_{s+1}(n)
        worst = inf
        for n in range(Lv):
            model = sum(cx.Psi(s, n // p, j1) * (1 - Lv * rho(s, n, j1))
                        for j1 in range(0, (Lv - 1 - n) // p + 1))
            model += Lv * sum(F(1, j) * cx.Xihat(s + 1, n, j) for j in range(1, Lv - n) if j % p)
            worst = min(worst, vp(cx.K(s + 1, n) - model, p))
        out(f"  step s={s}: min_n v_p(K_(s+1)(n) - first-order model) = {fv(worst)}, claimed >= {2*s+2}")
        must(f"step s={s}: model congruence mod p^(2s+2)", worst >= 2 * s + 2)
        Xs1 = sum(cx.sigma(sp, n) * cx.Hp(n) * cx.K(s, n // p) for n in range(Lv))
        Xs2 = sum(cx.sigma(sp, n) * sum(cx.Psi(s, n // p, j1) * cx.Hp(p * j1)
                                        for j1 in range(0, (Lv - 1 - n) // p + 1)) for n in range(Lv))
        Xs3 = sum(cx.sigma(sp, n) * sum(cx.Psi(s, n // p, j1) * cx.Hp(n + p * j1)
                                        for j1 in range(0, (Lv - 1 - n) // p + 1)) for n in range(Lv))
        Xs = sum(cx.sigma(sp, n) * sum(cx.Psi(s, n // p, j1) * rho(s, n, j1)
                                       for j1 in range(0, (Lv - 1 - n) // p + 1)) for n in range(Lv))
        Ys = sum(cx.sigma(sp, n) * sum(F(1, j) * cx.Xihat(s + 1, n, j) for j in range(1, Lv - n) if j % p)
                 for n in range(Lv))
        must(f"step s={s}: X_s = X_s1 - X_s2 + 2X_s3 (exact)", Xs == Xs1 - Xs2 + 2 * Xs3)
        check(f"step s={s}: X_(s,1) (claimed mod p^(2s'+1+s)={2*sp+1+s})", Xs1, p, 2 * sp + 1 + s)
        check(f"step s={s}: X_(s,2) (claimed mod p^(2s'+2+s)={2*sp+2+s})", Xs2, p, 2 * sp + 2 + s)
        check(f"step s={s}: X_(s,3) (claimed mod p^(2r-s-1)={2*r-s-1})", Xs3, p, 2 * r - s - 1)
        check(f"step s={s}: X_(s,3)-X_(s,2)-X_(s,1) (t>=1 tail; claimed mod p^(1+2s'+s)={1+2*sp+s})",
              Xs3 - Xs2 - Xs1, p, 1 + 2 * sp + s)
        check(f"step s={s}: Y_s (claimed mod p^(2s'+s+1)={2*sp+s+1})", Ys, p, 2 * sp + s + 1)
        check(f"step s={s}: A_(s+1) - (A_s - L X_s + L Y_s) (claimed mod p^(2r))",
              A[s + 1] - (A[s] - Lv * Xs + Lv * Ys), p, 2 * r)
        # Lemma 2.7(Y) cell hypothesis for the Y_s weights, t = 1, 2 (all cells inside [0, L_{s+1}))
        for t in (1, 2):
            if p ** t > Lv:
                continue
            nb = Lv // p ** t
            worst = inf
            for i in range(nb):
                for ip in range(nb):
                    for c in (0, 1):
                        tot = F(0)
                        for n in range(i * p ** t, (i + 1) * p ** t):
                            nbar = n % p ** t
                            for j in range(ip * p ** t, (ip + 1) * p ** t):
                                if j % p == 0:
                                    continue
                                if int(nbar + j % p ** t >= p ** t) != c:
                                    continue
                                tot += cx.sigma(sp, n) / j
                        worst = min(worst, vp(tot, p))
            out(f"  step s={s}: Lemma 2.7(Y) cells at t={t}, s'={sp}: min v_p = {fv(worst)}, claimed >= {2*sp+t}")
            must(f"step s={s}: Lemma 2.7(Y) cell hypothesis t={t}", worst >= 2 * sp + t)
    return SigK


# ----------------------------------------------------------------------------
# section 5: class J
# ----------------------------------------------------------------------------
def section5(cx):
    p, r, m, N, M = cx.p, cx.r, cx.m, cx.N, cx.M
    out("--- Section 5 (class J) ---")
    SigJ = sum(cx.Stilde(N, k, j) for k in range(0, N, p) for j in range(1, N - k) if j % p)
    # exact factorization S~(N; pk1, j) = (N/(N+j)) Phi_r(pk1, j)
    bad = [(k, j) for k in range(0, N, p) for j in range(1, N - k) if j % p
           and cx.Stilde(N, k, j) != F(N, N + j) * cx.Phi(r, k, j)]
    must("S~(N;pk1,j) = (N/(N+j)) Phi_r(pk1,j) exactly", not bad)
    T1 = sum(F(1, j) * cx.Khatprime(r, j) for j in range(1, N) if j % p)
    T2 = sum(F(1, j * j) * cx.Khatprime(r, j) for j in range(1, N) if j % p)
    check("(iv): Sigma_J - [N sum'(1/j)K^'_r - N^2 sum'(1/j^2)K^'_r]", SigJ - N * T1 + N * N * T2, p, 3 * r)
    check("sum'_{j<N} (1/j^2) K^'_r(j)", T2, p, r)
    bad = [j for j in range(1, N) if j % p and vp(cx.Khatprime(r, j) - cx.Kprime(r - 1, j // p), p) < r]
    must("tower: K^'_r(j) = K'_{r-1}([j/p]) mod p^r for p-free j", not bad)

    # (ii): exact product identity and the FIRST-ORDER COEFFICIENT (sign check)
    def rho_note(u, j, k1):   # as printed in the note: H'_j - H'_{pk1} + 2H'_{j+pk1}
        return cx.Hp(j) - cx.Hp(p * k1) + 2 * cx.Hp(j + p * k1)

    def rho_corr(u, j, k1):   # from Lemma 1.3 applied to P^2_{pk1} Pbar_{pk1} P^2_{pk1+j} Pbar_j
        return cx.Hp(p * k1) - cx.Hp(j) + 2 * cx.Hp(j + p * k1)

    for u in range(0, r):
        Lv = cx.L[u + 1]
        exact_ok = True
        w_note, w_corr = inf, inf
        for k1 in range(0, cx.L[u]):
            for j in range(0, Lv - p * k1):
                lhs = cx.Phi(u + 1, p * k1, j)
                E = (cx.P(Lv, p * k1) ** 2 * cx.Pbar(Lv, p * k1)
                     * cx.P(Lv, p * k1 + j) ** 2 * cx.Pbar(Lv, j))
                base = cx.Phi(u, k1, j // p)
                if lhs != base * E:
                    exact_ok = False
                w_note = min(w_note, vp(lhs - base * (1 - Lv * rho_note(u, j, k1)), p))
                w_corr = min(w_corr, vp(lhs - base * (1 - Lv * rho_corr(u, j, k1)), p))
        must(f"(ii) exact identity Phi_(u+1)(pk1,j) = Phi_u(k1,[j/p]) P^2 Pbar P^2 Pbar at u={u}", exact_ok)
        out(f"  (ii) u={u}: first-order model mod p^(2u+2)={2*u+2}: with the NOTE's rho' "
            f"(H'_j - H'_pk1 + 2H'_(j+pk1)) min v_p = {fv(w_note)}; with rho' = H'_pk1 - H'_j + 2H'_(j+pk1) "
            f"min v_p = {fv(w_corr)}")
        must(f"(ii) u={u}: corrected rho' gives the congruence mod p^(2u+2)", w_corr >= 2 * u + 2)
        if w_note < 2 * u + 2:
            out(f"  NOTE: the printed rho'_u(j,k1) is WRONG at u={u} (sign of H'_j and H'_pk1 swapped)")

    # (i) carry tower Xi^'_u(k,j) = Xi_{u-1}^{(delta)}([k/p],[j/p]) mod p^u, p-free k, all j
    for u in range(1, r + 1):
        Lu = cx.L[u]
        bad = []
        for k in range(1, Lu):
            if k % p == 0:
                continue
            for j in range(0, Lu - k):
                delta = int((k % p) + (j % p) >= p)
                if vp(cx.Xihatprime(u, k, j) - cx.Xi(u - 1, delta, k // p, j // p), p) < u:
                    bad.append((k, j))
        must(f"(i) Xi^'_u(k,j) = Xi_(u-1)^(delta)([k/p],[j/p]) mod p^u at u={u}", not bad)
    # (iii) moment kernels sum_k k^t Phi_u(k,j) = 0 mod p^u (t = 1, 2, 3) and K~' tower
    for u in range(1, r + 1):
        Lu = cx.L[u]
        worst = inf
        for j in range(Lu):
            for t in (1, 2, 3):
                worst = min(worst, vp(sum(k ** t * cx.Phi(u, k, j) for k in range(Lu - j)), p))
        out(f"  (iii) u={u}: moment kernels sum_k k^t Phi_u(k,j), t=1..3: min v_p = {fv(worst)}, claimed >= {u}")
        must(f"(iii) moment kernels for Phi at u={u}", worst >= u)
        bad = []
        for j in range(Lu):
            lhs = sum(cx.Phi(u, k, j) * cx.Hp(p * k) for k in range(Lu - j))
            rhs = sum(cx.Phi(u - 1, k1, j // p) * cx.Hp(p * p * k1) for k1 in range(cx.L[u - 1] - j // p))
            if vp(lhs - rhs, p) < u:
                bad.append(j)
        must(f"(iii) harmonically weighted tower for Phi (d=1) at u={u}", not bad)

    # A'_s, X^', pieces (with the corrected rho')
    A = {s: sum(cx.sigma(r - s, j) * cx.Kprime(s, j) for j in range(cx.L[s])) for s in range(r)}
    for s in range(r):
        check(f"A'_{s} (claimed mod p^(2r))", A[s], p, 2 * r)
    Xhat_c = sum(F(1, j) * sum(cx.Phi(r - 1, k1, j // p) * rho_corr(r - 1, j, k1)
                               for k1 in range(0, (N - 1 - j) // p + 1)) for j in range(1, N) if j % p)
    Xhat_n = sum(F(1, j) * sum(cx.Phi(r - 1, k1, j // p) * rho_note(r - 1, j, k1)
                               for k1 in range(0, (N - 1 - j) // p + 1)) for j in range(1, N) if j % p)
    check("(4.2)': sum'(1/j)K^'_r - (A'_{r-1} - N X^') with corrected rho'", T1 - (A[r - 1] - N * Xhat_c), p, 2 * r)
    out(f"  (for comparison, with the note's rho': v_p = {fv(vp(T1 - (A[r-1] - N*Xhat_n), p))}, needs >= {2*r})")
    check("X^' (corrected rho')", Xhat_c, p, r)
    X1 = sum(F(1, j) * cx.Hp(j) * cx.Kprime(r - 1, j // p) for j in range(1, N) if j % p)
    X2 = sum(F(1, j) * sum(cx.Phi(r - 1, k1, j // p) * cx.Hp(p * k1)
                           for k1 in range(0, (N - 1 - j) // p + 1)) for j in range(1, N) if j % p)
    X3 = sum(F(1, j) * sum(cx.Phi(r - 1, k1, j // p) * cx.Hp(j + p * k1)
                           for k1 in range(0, (N - 1 - j) // p + 1)) for j in range(1, N) if j % p)
    must("X^' = -X^'_1 + X^'_2 + 2X^'_3 (exact, corrected signs)", Xhat_c == -X1 + X2 + 2 * X3)
    check("X^'_1", X1, p, r)
    check("X^'_2 (claimed mod p^(r+1))", X2, p, r + 1)
    check("X^'_3", X3, p, r)
    for s in range(0, r - 1):
        sp = r - s - 1
        Lv = cx.L[s + 1]
        Xs1 = sum(cx.sigma(sp, j) * cx.Hp(j) * cx.Kprime(s, j // p) for j in range(Lv))
        Xs2 = sum(cx.sigma(sp, j) * sum(cx.Phi(s, k1, j // p) * cx.Hp(p * k1)
                                        for k1 in range(0, (Lv - 1 - j) // p + 1)) for j in range(Lv))
        Xs3 = sum(cx.sigma(sp, j) * sum(cx.Phi(s, k1, j // p) * cx.Hp(j + p * k1)
                                        for k1 in range(0, (Lv - 1 - j) // p + 1)) for j in range(Lv))
        Xs = -Xs1 + Xs2 + 2 * Xs3
        Ys = sum(cx.sigma(sp, j) * sum(F(1, k) * cx.Xihatprime(s + 1, k, j) for k in range(1, Lv - j) if k % p)
                 for j in range(Lv))
        check(f"step s={s}: X'_(s,1)", Xs1, p, 2 * sp + 1 + s)
        check(f"step s={s}: X'_(s,2)", Xs2, p, 2 * sp + 2 + s)
        check(f"step s={s}: X'_(s,3)", Xs3, p, 2 * r - s - 1)
        check(f"step s={s}: Y'_s", Ys, p, 2 * sp + s + 1)
        check(f"step s={s}: A'_(s+1) - (A'_s - L X'_s + L Y'_s) (corrected rho')",
              A[s + 1] - (A[s] - Lv * Xs + Lv * Ys), p, 2 * r)
    return SigJ


# ----------------------------------------------------------------------------
# section 6: class B
# ----------------------------------------------------------------------------
def section6(cx):
    p, r, N = cx.p, cx.r, cx.N
    out("--- Section 6 (class B) ---")
    SigB = sum(cx.Stilde(N, k, j) for k in range(1, N) if k % p for j in range(1, N - k) if j % p)
    inner = sum(F(1, k * j) * cx.Xihat(r, k, j) for k in range(1, N) if k % p for j in range(1, N - k) if j % p)
    check("Sigma_B - N^2 sum' Xi^_r(k,j)/(kj)", SigB - N * N * inner, p, 3 * r)
    check("sum' Xi^_r(k,j)/(kj)", inner, p, r)
    # Lemma 2.7(B) cells, t = 1, 2
    for t in (1, 2):
        if p ** t > N:
            continue
        nb = N // p ** t
        worst = inf
        for i in range(nb):
            for ip in range(nb):
                for c in (0, 1):
                    tot = F(0)
                    for k in range(i * p ** t, (i + 1) * p ** t):
                        if k % p == 0:
                            continue
                        kb = k % p ** t
                        for j in range(ip * p ** t, (ip + 1) * p ** t):
                            if j % p == 0 or int(kb + j % p ** t >= p ** t) != c:
                                continue
                            tot += F(1, k * j)
                    worst = min(worst, vp(tot, p))
        out(f"  Lemma 2.7(B) cells at t={t}: min v_p = {fv(worst)}, claimed >= {t}")
        must(f"Lemma 2.7(B) cell hypothesis t={t}", worst >= t)
    return SigB


# ----------------------------------------------------------------------------
# section 7: class S
# ----------------------------------------------------------------------------
def section7(cx):
    p, r, m, N, M = cx.p, cx.r, cx.m, cx.N, cx.M
    out("--- Section 7 (class S) ---")
    aM = a_of(cx, M)
    SigS = sum(cx.Stilde(N, p * kp, p * jp) for kp in range(M) for jp in range(M - kp))
    # exact factorization
    bad = []
    for kp in range(M):
        for jp in range(M - kp):
            E = (cx.P(N, p * kp) ** 2 * cx.Pbar(N, p * kp)
                 * cx.P(N, p * (kp + jp)) ** 2 * cx.Pbar(N, p * jp))
            if cx.Stilde(N, p * kp, p * jp) != cx.Stilde(M, kp, jp) * E:
                bad.append((kp, jp))
    must("S~(N;pk',pj') = S~(M;k',j') E exactly", not bad)

    def rhoS(kp, jp):
        return cx.Hp(p * kp) + 2 * cx.Hp(p * (kp + jp)) - cx.Hp(p * jp)

    TS = sum(cx.Stilde(M, kp, jp) * rhoS(kp, jp) for kp in range(M) for jp in range(M - kp))
    check("Step 1: (Sigma_S - a(M-1)) + N T_S", SigS - aM + N * TS, p, 3 * r)
    # Step 1 termwise: S~(M) (E - 1 + N rho_S) mod p^{3r}
    worst = inf
    for kp in range(M):
        for jp in range(M - kp):
            base = cx.Stilde(M, kp, jp)
            if base == 0:
                continue
            E = (cx.P(N, p * kp) ** 2 * cx.Pbar(N, p * kp)
                 * cx.P(N, p * (kp + jp)) ** 2 * cx.Pbar(N, p * jp))
            worst = min(worst, vp(base * (E - 1 + N * rhoS(kp, jp)), p))
    out(f"  Step 1 termwise: min v_p(S~(M;k',j')(E - 1 + N rho_S)) = {fv(worst)}, claimed >= {3*r}")
    must("Step 1 termwise second-order bound", worst >= 3 * r)
    # Step 2
    worstZ = inf
    for kp in range(1, M):
        for jp in range(1, M):
            Z = sum(F(1, mu * (mu + p * kp)) for mu in range(1, p * jp + 1) if mu % p)
            b = vp(jp, p)
            worstZ = min(worstZ, vp(Z, p) - (1 + b))
    out(f"  Step 2: min over k',j' of v_p(Z) - (1+b) = {fv(worstZ)}, claimed >= 0")
    must("Step 2: v(Z) >= 1 + b", worstZ >= 0)
    T1 = sum(cx.Stilde(M, kp, jp) * cx.Hp(p * kp) for kp in range(M) for jp in range(M - kp))
    T2 = sum(cx.Stilde(M, kp, jp) * cx.Hp(p * jp) for kp in range(M) for jp in range(M - kp))
    check("Step 2: T_S - 3T_1 - T_2", TS - 3 * T1 - T2, p, 2 * r)
    check("T_1", T1, p, 2 * r)
    check("T_2", T2, p, 2 * r)

    # Step 3: strata of T_1
    def G1(u, x):
        Lu = cx.L[u]
        return sum(C(Lu - 1, x + j) ** 2 * C(Lu + j - 1, j) for j in range(0, max(0, Lu - x)))

    def R1(u, kap):
        Lu = cx.L[u]
        return C(Lu - 1, kap) ** 2 * (-1) ** (kap - 1) * C(-Lu - 1, kap - 1) * G1(u, kap)

    def G2(u, y):
        Lu = cx.L[u]
        return sum(C(Lu - 1, k) ** 2 * C(Lu + k - 1, k) * C(Lu - 1, k + y) ** 2 for k in range(0, max(0, Lu - y)))

    def R2(u, io):
        Lu = cx.L[u]
        return (-1) ** (io - 1) * C(-Lu - 1, io - 1) * G2(u, io)

    strata1 = {}
    strata2 = {}
    for kp in range(1, M):
        s = vp(p * kp, p)
        strata1[s] = strata1.get(s, 0) + cx.Hp(p * kp) * C(M - 1, kp) ** 2 * C(M + kp - 1, kp) * G1(r - 1, kp)
        strata2[s] = strata2.get(s, 0) + cx.Hp(p * kp) * C(M + kp - 1, kp) * G2(r - 1, kp)
    must("T_1 = sum of strata (exact)", sum(strata1.values()) == T1)
    must("T_2 = sum of strata (exact)", sum(strata2.values()) == T2)
    for s in sorted(strata1):
        check(f"Step 3: T_1 stratum sigma={s}", strata1[s], p, 2 * r)
        check(f"Step 4: T_2 stratum sigma={s}", strata2[s], p, 2 * r)
        if s <= r - 1:
            u = r - s
            Lu = cx.L[u]
            red1 = m * p ** u * sum(F(1, kap) * cx.Hp(p ** s * kap) * R1(u, kap) for kap in range(1, Lu) if kap % p)
            red2 = m * p ** u * sum(F(1, kap) * cx.Hp(p ** s * kap) * R2(u, kap) for kap in range(1, Lu) if kap % p)
            check(f"  sigma={s}: T_1 stratum - reduced form m p^(r-sigma) sum' (1/kappa) H'_(p^sigma kappa) R^(r-sigma)",
                  strata1[s] - red1, p, 2 * r)
            check(f"  sigma={s}: T_2 stratum - reduced form (R_2)", strata2[s] - red2, p, 2 * r)
            a_int = all(vp(F(1, kap) * cx.Hp(p ** s * kap), p) >= 2 * s for kap in range(1, Lu) if kap % p)
            must(f"  sigma={s}: a_kappa = p^(-2sigma)(1/kappa)H'_(p^sigma kappa) integral", a_int)
            inner1 = sum(F(1, kap) * cx.Hp(p ** s * kap) * R1(u, kap) for kap in range(1, Lu) if kap % p) / p ** (2 * s)
            inner2 = sum(F(1, kap) * cx.Hp(p ** s * kap) * R2(u, kap) for kap in range(1, Lu) if kap % p) / p ** (2 * s)
            check(f"  sigma={s}: sum' a_kappa R^(r-sigma)(kappa) (Lemma 3.1 output, claimed mod p^(r-sigma)={u})", inner1, p, u)
            check(f"  sigma={s}: sum' a_iota R_2^(r-sigma)(iota) (claimed mod p^(r-sigma)={u})", inner2, p, u)
            # Lemma 2.6 input: block sums of a_kappa at t = 1
            if p <= Lu:
                worst = inf
                for i in range(Lu // p):
                    tot = sum(F(1, kap) * cx.Hp(p ** s * kap) for kap in range(i * p, (i + 1) * p) if kap % p)
                    worst = min(worst, vp(tot, p))
                out(f"  sigma={s}: Lemma 2.6 block sums (t=1, s=sigma): min v_p = {fv(worst)}, claimed >= {1+2*s}")
                must(f"  sigma={s}: Lemma 2.6 strong form at t=1", worst >= 1 + 2 * s)
            # kernel tower at the top: R^(u)(kappa) = R^^(u-1)([kappa/p]) mod p^u for p-free kappa
            if u >= 1:
                def R1hat(w, q):
                    Lw = cx.L[w]
                    return C(Lw - 1, q) ** 2 * (-1) ** q * C(-Lw - 1, q) * G1(w, q)
                bad = [kap for kap in range(1, Lu) if kap % p and vp(R1(u, kap) - R1hat(u - 1, kap // p), p) < u]
                must(f"  sigma={s}: R^(u)(kappa) = R^^(u-1)([kappa/p]) mod p^u (u={u}) on units", not bad)
    return SigS, aM


# ----------------------------------------------------------------------------
def run(p, r, m):
    cx = Ctx(p, r, m)
    out("=" * 78)
    out(f"(p, r, m) = ({p}, {r}, {m}); N = {cx.N}, M = {cx.M}")
    out("=" * 78)
    sums = class_sums(cx)
    aN = a_of(cx, cx.N)
    aM = a_of(cx, cx.M)
    must("a(N-1) = Sigma_S + Sigma_K + Sigma_J + Sigma_B (exact)", aN == sum(sums.values()))
    check("Theorem: a(N-1) - a(M-1)", aN - aM, p, 3 * r)
    check("(S): Sigma_S - a(M-1)", sums["S"] - aM, p, 3 * r)
    check("(K): Sigma_K", sums["K"], p, 3 * r)
    check("(J): Sigma_J", sums["J"], p, 3 * r)
    check("(B): Sigma_B", sums["B"], p, 3 * r)
    SigK = section4(cx)
    must("Section 4 recomputed Sigma_K agrees with the class split", SigK == sums["K"])
    SigJ = section5(cx)
    must("Section 5 recomputed Sigma_J agrees with the class split", SigJ == sums["J"])
    SigB = section6(cx)
    must("Section 6 recomputed Sigma_B agrees with the class split", SigB == sums["B"])
    SigS, aM2 = section7(cx)
    must("Section 7 recomputed Sigma_S agrees with the class split", SigS == sums["S"] and aM2 == aM)
    out("")


def main():
    cases = [(5, 2, 1), (5, 2, 2), (7, 2, 1), (5, 3, 1)]
    for case in cases:
        run(*case)
    out("=" * 78)
    if FAILS:
        out(f"FAILURES ({len(FAILS)}):")
        for f_ in FAILS:
            out("  - " + f_)
    else:
        out("No structural failures. (Lines marked FAIL above, if any, are valuation shortfalls.)")
    here = os.path.dirname(os.path.abspath(__file__))
    outdir = os.path.join(here, "out")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "referee_B_shifted_assembly.txt"), "w") as fh:
        fh.write("\n".join(LINES) + "\n")


if __name__ == "__main__":
    main()
