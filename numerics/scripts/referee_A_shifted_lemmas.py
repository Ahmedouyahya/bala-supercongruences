#!/usr/bin/env python3
"""Referee A -- independent numerical checks of Sections 0-3 of
notes/A376462-shifted-congruence-proof.md (conventions, Lemmas 1.2, 1.3, 2.1, 2.3,
2.5, 2.6, 2.7, 3.2 (carry composition), 3.3, 3.4, 3.5).

Everything is exact: Python integers and fractions.Fraction; valuations are read off
numerators/denominators.  Nothing is imported from the project's own scripts.

Output: numerics/out/referee_A_shifted_lemmas.txt
"""
from fractions import Fraction as Fr
from math import comb
import os, sys, time

INF = float('inf')
HERE = os.path.dirname(os.path.abspath(__file__))
OUTPATH = os.path.join(HERE, 'out', 'referee_A_shifted_lemmas.txt')
LINES, FAILS = [], []

def out(s=''):
    print(s); LINES.append(s)

def record(name, ok, detail=''):
    if not ok:
        FAILS.append((name, detail))
    out(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ''))

# ----------------------------------------------------------------------------- basics
def vp_int(n, p):
    if n == 0:
        return INF
    v = 0
    while n % p == 0:
        n //= p; v += 1
    return v

def vp(x, p):
    if isinstance(x, int):
        return vp_int(x, p)
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)

def C(a, b):
    """Generalized binomial, a in Z, b in Z (Section 0 convention)."""
    if b < 0:
        return 0
    if a >= 0:
        return comb(a, b)
    return (-1) ** b * comb(-a + b - 1, b)

class Harm:
    """H'_n = sum_{lambda<=n, p∤lambda} 1/lambda, sigma_t(n), S_d(x)."""
    def __init__(self, p):
        self.p = p
        self.H = [Fr(0)]
    def ensure(self, N):
        H, p = self.H, self.p
        while len(H) <= N:
            n = len(H)
            H.append(H[-1] + (Fr(1, n) if n % p else 0))
    def Hp(self, n):
        if n < 0:
            return Fr(0)
        self.ensure(n)
        return self.H[n]
    def sigma(self, t, n):
        pt = self.p ** t
        return self.Hp((n + 1) * pt - 1) - self.Hp(n * pt - 1)
    def S(self, d, x):
        return sum((Fr(1, mu ** d) for mu in range(1, x + 1) if mu % self.p), Fr(0))

HARM = {}
def harm(p):
    if p not in HARM:
        HARM[p] = Harm(p)
    return HARM[p]

def fmt_v(v):
    return 'inf' if v == INF else str(v)

# ============================================================================ A. Lemma 1.2
def section_A():
    out("\n=== A. Lemma 1.2 (a),(b) for NEGATIVE and positive m, incl. the 'consequence' at index n-1 ===")
    worst = INF
    for p in (5, 7):
        for m in (-3, -2, -1, 1, 2, 3):
            for s in (1, 2, 3):
                L, Lp = m * p ** s, m * p ** (s - 1)
                ok_a = ok_b = ok_c = True
                for n in range(0, 3 * p ** s + 2):
                    lhs = (-1) ** n * C(L - 1, n)
                    rhs = (-1) ** (n // p) * C(Lp - 1, n // p)
                    if vp_int(lhs - rhs, p) < s:
                        ok_a = False
                    worst = min(worst, vp_int(lhs - rhs, p) - s)
                    if vp_int(C(L, p * n) - C(Lp, n), p) < s:
                        ok_b = False
                    if n % p:   # consequence after Lemma 1.2
                        lhs = (-1) ** (n - 1) * C(L - 1, n - 1)
                        rhs = (-1) ** (n // p) * C(Lp - 1, n // p)
                        if vp_int(lhs - rhs, p) < s:
                            ok_c = False
                record(f"L1.2(a) p={p} m={m} s={s}", ok_a)
                record(f"L1.2(b) p={p} m={m} s={s}", ok_b)
                record(f"L1.2 consequence (index n-1, p∤n) p={p} m={m} s={s}", ok_c)
    out(f"  min slack over all L1.2(a) checks: {worst} (0 means the modulus p^s is sharp somewhere)")

# ============================================================================ B. Lemma 1.3
def poly_mul_lin(poly, a, D):
    """poly * (1 + a*L), truncated at degree D."""
    new = poly[:]
    for k in range(1, D + 1):
        new[k] += a * poly[k - 1]
    return new

def section_B():
    out("\n=== B. Lemma 1.3: e_1, e_2 formulas (re-derived by polynomial expansion in L), integrality ===")
    D = 3
    configs = [
        # (p, [(x_i,a_i)], [(y_i,b_i)])
        (5, [(7, 2), (12, 2)], [(7, 1), (10, 1)]),      # shape of Lemma 3.5's E
        (5, [(23, 2), (33, 2)], [(23, 1), (10, 1)]),
        (7, [(9, 1), (20, 3)], [(4, 2), (31, 1)]),
        (7, [(50, 2), (57, 2)], [(50, 1), (7, 1)]),
        (5, [(0, 2)], [(13, 1)]),
        (11, [(12, 2), (25, 2)], [(12, 1), (13, 1)]),
    ]
    for (p, A, B) in configs:
        h = harm(p)
        poly = [Fr(1)] + [Fr(0)] * D
        for (x, a) in A:
            for lam in range(1, x + 1):
                if lam % p:
                    for _ in range(a):
                        poly = poly_mul_lin(poly, Fr(-1, lam), D)
        for (y, b) in B:
            for lam in range(1, y + 1):
                if lam % p:
                    for _ in range(b):
                        poly = poly_mul_lin(poly, Fr(1, lam), D)
        e1 = -sum(a * h.Hp(x) for (x, a) in A) + sum(b * h.Hp(y) for (y, b) in B)
        e2 = Fr(1, 2) * e1 ** 2 - Fr(1, 2) * (sum(a * h.S(2, x) for (x, a) in A) + sum(b * h.S(2, y) for (y, b) in B))
        record(f"L1.3 e_1 formula p={p} A={A} B={B}", poly[1] == e1)
        record(f"L1.3 e_2 formula p={p} A={A} B={B}", poly[2] == e2)
        record(f"L1.3 e_0..e_3 p-integral p={p}", all(vp(c, p) >= 0 for c in poly), f"vals {[fmt_v(vp(c,p)) for c in poly]}")

# ============================================================================ C. Lemma 2.1
def e_of(d, p):
    return 0 if d % (p - 1) else 1 + vp_int(d, p)

def section_C():
    out("\n=== C. Lemma 2.1: sum over (Z/p^v)^x of u^{-d} mod p^{v-e(d)}; S_d(p^v y); block sums of k^{-2} ===")
    for p in (5, 7, 11, 13):
        ds = list(range(1, 2 * (p - 1) + 1)) + [(p - 1) * p, (p - 1) * p * 2, (p - 1) * p * p, (p - 1) * (p + 1)]
        for v in (1, 2, 3, 4):
            if p ** v > 30000:
                continue
            mod = p ** v
            bad = []
            tight = []
            for d in ds:
                s = sum(pow(u, -d, mod) for u in range(1, mod) if u % p) % mod
                e = e_of(d, p)
                need = max(v - e, 0)
                got = v if s == 0 else vp_int(s, p)   # 'v' means: 0 mod p^v, cannot see beyond
                if got < need:
                    bad.append((d, got, need))
                if got == need and need < v:
                    tight.append(d)
            record(f"L2.1 group sum p={p} v={v}, d in {len(ds)} values incl. (p-1)|d", not bad,
                   f"violations {bad}" if bad else f"tight (valuation exactly v-e(d)) at d={tight}")
    # S_d(x) with x = p^v y, exact fractions, and block sums of k^{-2}
    for p in (5, 7, 11):
        h = harm(p)
        for v in (1, 2):
            for y in (1, 2, 3):
                x = p ** v * y
                bad = []
                for d in (1, 2, 3, p - 1, p, 2 * (p - 1), (p - 1) * p):
                    val = vp(h.S(d, x), p)
                    if val < v - e_of(d, p):
                        bad.append((d, fmt_v(val), v - e_of(d, p)))
                record(f"L2.1 S_d(p^v y) p={p} v={v} y={y}", not bad, str(bad) if bad else '')
            for l in range(0, 4):
                blk = sum((Fr(1, k * k) for k in range(l * p ** v, (l + 1) * p ** v) if k % p), Fr(0))
                record(f"L2.1 block sum k^-2 over B_{v}({l}) p={p}", vp(blk, p) >= v, f"v_p={fmt_v(vp(blk,p))} need {v}")

# ============================================================================ D. Lemma 2.3
def section_D():
    out("\n=== D. Lemma 2.3 (reflection), both claims ===")
    for p in (5, 7):
        h = harm(p)
        for t in (1, 2):
            pt = p ** t
            ok = True; worst = INF
            for n in range(0, pt):
                tail = sum((Fr(1, mu * mu) for mu in range(n + 1, pt) if mu % p), Fr(0))
                val = vp(h.Hp(pt - 1 - n) - h.Hp(n) + pt * tail, p)
                worst = min(worst, val - 2 * t)
                if val < 2 * t:
                    ok = False
            record(f"L2.3 first claim p={p} t={t} (all n<p^t)", ok, f"min slack {fmt_v(worst)}")
            for s in (1, 2):
                ok = True; worst = INF
                for k in range(0, pt + 1):
                    val = vp(h.Hp((pt - k) * p ** s) - h.Hp(k * p ** s), p)
                    worst = min(worst, val - (t + 2 * s))
                    if val < t + 2 * s:
                        ok = False
                record(f"L2.3 second claim p={p} t={t} s={s} (all 0<=k<=p^t)", ok, f"min slack {fmt_v(worst)}")

# ============================================================================ E. Lemma 2.5
def section_E():
    out("\n=== E. Lemma 2.5: sum_{n in B_t(i)} sigma_s(n) H'_n == 0 mod p^{t+2s} ===")
    for p in (5, 7, 11):
        h = harm(p)
        for s in (0, 1, 2):
            for t in (0, 1, 2):
                if p == 11 and s + t > 2:
                    continue
                for i in (0, 1, 2, 3):
                    if p == 11 and i > 2:
                        continue
                    tot = sum((h.sigma(s, n) * h.Hp(n) for n in range(i * p ** t, (i + 1) * p ** t)), Fr(0))
                    val = vp(tot, p)
                    record(f"L2.5 p={p} s={s} t={t} i={i}", val >= t + 2 * s, f"v_p={fmt_v(val)} need {t+2*s}")

    out("\n--- E.1 the floor identity used in the base block: [(p^{t'}-k)/p^s] == p^t-1-[k/p^s] for p∤k ---")
    for p in (5, 7):
        for s in (0, 1, 2):
            for t in (1, 2):
                tp = t + s
                holds = all(((p ** tp - k) // p ** s) == p ** t - 1 - k // p ** s
                            for k in range(1, p ** tp) if k % p)
                out(f"  p={p} s={s} t={t}: identity holds for all units k: {holds}"
                    + ("" if holds else "   <-- FALSE for s=0: [(p^t-k)] = p^t-k = (p^t-1-k)+1"))

    out("\n--- E.2 general-block error terms of the written proof (k = i p^{t'} + kbar) ---")
    out("    eps1(kbar) := (H'_{n(k)} - H'_{i p^t} - H'_{nbar})/p^t,  eps2(kbar) := (1/k - 1/kbar)/p^{t'}")
    out("    cross term X := p^{t+t'} * sum' eps2*eps1 ; proof claims only 'carries p^{t+t'}', need p^{t+2s}")
    for p in (5, 7):
        h = harm(p)
        for (s, t) in ((1, 1), (2, 1), (2, 2), (1, 2), (3, 1)):
            if p == 7 and s == 3:
                continue
            tp = t + s
            for i in (1, 2):
                cross = Fr(0); repl = Fr(0)
                for kb in range(1, p ** tp):
                    if kb % p == 0:
                        continue
                    k = i * p ** tp + kb
                    nb = kb // p ** s
                    n = k // p ** s
                    eps1 = (h.Hp(n) - h.Hp(i * p ** t) - h.Hp(nb)) / p ** t
                    eps2 = (Fr(1, k) - Fr(1, kb)) / p ** tp
                    cross += eps2 * eps1
                    repl += Fr(1, kb) * (eps1 + i * h.S(2, nb))   # error of replacing eps1 by -i S_2(nbar)
                vX = vp(p ** (t + tp) * cross, p)
                vR = vp(p ** t * repl, p)
                out(f"  p={p} s={s} t={t} i={i}: v_p(cross term)={fmt_v(vX)}  [claimed bound t+t'={t+tp}, needed t+2s={t+2*s}];"
                    f"  v_p(p^t*sum'(1/kbar)(eps1+i S_2(nbar)))={fmt_v(vR)} [needed {t+2*s}]")
                record(f"L2.5 cross term actually has v_p >= t+2s (p={p},s={s},t={t},i={i})", vX >= t + 2 * s)
                if t + tp < t + 2 * s:
                    out(f"      NOTE: the stated bound p^{{t+t'}} = p^{t+tp} is weaker than the required p^{t+2*s}: proof gap (true, but not proved as written).")

# ============================================================================ F. Lemma 2.6
def section_F():
    out("\n=== F. Lemma 2.6 (strong form): sum'_{k in B_t(i)} (1/k) H'_{k p^s} == 0 mod p^{t+2s} ===")
    for p in (5, 7, 11):
        h = harm(p)
        for s in (0, 1, 2):
            for t in (0, 1, 2):
                if p == 11 and s + t > 2:
                    continue
                for i in (0, 1, 2, 3):
                    if p == 11 and i > 2:
                        continue
                    tot = sum((Fr(1, k) * h.Hp(k * p ** s) for k in range(i * p ** t, (i + 1) * p ** t) if k % p), Fr(0))
                    val = vp(tot, p)
                    record(f"L2.6 p={p} s={s} t={t} i={i}", val >= t + 2 * s, f"v_p={fmt_v(val)} need {t+2*s}")

# ============================================================================ G. Lemma 2.7
def section_G():
    out("\n=== G. Lemma 2.7 (Y) and (B), carry-restricted cells ===")
    pairs = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (1, 2), (2, 2), (3, 1)]
    for p in (5, 7):
        h = harm(p)
        for t in (1, 2):
            pt = p ** t
            for sp in (0, 1, 2):
                for (i, ip) in pairs:
                    for c in (0, 1):
                        tot = Fr(0)
                        if p == 5 and t == 1:
                            # brute force
                            for n in range(i * pt, (i + 1) * pt):
                                sn = h.sigma(sp, n); nb = n % pt
                                for j in range(ip * pt, (ip + 1) * pt):
                                    if j % p and int(nb + j % pt >= pt) == c:
                                        tot += sn / j
                        else:
                            # exact prefix-sum form of the inner j-sum
                            for n in range(i * pt, (i + 1) * pt):
                                sn = h.sigma(sp, n); nb = n % pt
                                split = ip * pt + pt - nb   # first j in the block with carry
                                if c == 1:
                                    inner = h.Hp((ip + 1) * pt - 1) - h.Hp(split - 1)
                                else:
                                    inner = h.Hp(split - 1) - h.Hp(ip * pt - 1)
                                tot += sn * inner
                        val = vp(tot, p)
                        record(f"L2.7(Y) p={p} t={t} s'={sp} cell({i},{ip};c={c})", val >= 2 * sp + t, f"v_p={fmt_v(val)} need {2*sp+t}")
            for (i, ip) in pairs:
                for c in (0, 1):
                    tot = Fr(0)
                    for k in range(i * pt, (i + 1) * pt):
                        if k % p == 0:
                            continue
                        kb = k % pt
                        for j in range(ip * pt, (ip + 1) * pt):
                            if j % p and int(kb + j % pt >= pt) == c:
                                tot += Fr(1, k * j)
                    val = vp(tot, p)
                    record(f"L2.7(B) p={p} t={t} cell({i},{ip};c={c})", val >= t, f"v_p={fmt_v(val)} need {t}")

# ============================================================================ H. Lemma 3.2 carries
def section_H():
    out("\n=== H. Lemma 3.2: carry composition identity (brute force) ===")
    for p in (5, 7):
        for t in (2, 3):
            pt, pt1 = p ** t, p ** (t - 1)
            ok = True
            for q in range(0, 2 * pt):
                for qp in range(0, 2 * pt):
                    for d in (0, 1):
                        d1 = int((q % p) + (qp % p) + d >= p)
                        lhs = int((q % pt) + (qp % pt) + d >= pt)
                        rhs = int(((q // p) % pt1) + ((qp // p) % pt1) + d1 >= pt1)
                        if lhs != rhs:
                            ok = False
            record(f"carry composition p={p} t={t} (all q,q'<2p^t, delta)", ok)

# ============================================================================ kernels
PSI = {}
def Psi(L, n, j):
    key = (L, n, j)
    if key not in PSI:
        PSI[key] = C(L - 1, n) ** 2 * (-1) ** n * C(-L - 1, n) * C(L - 1, n + j) ** 2 * (-1) ** j * C(-L, j)
    return PSI[key]

def Xi(L, d, q, qp):
    return C(L - 1, q) ** 2 * (-1) ** q * C(-L - 1, q) * C(L - 1, q + qp + d) ** 2 * (-1) ** qp * C(-L - 1, qp)

def Xihat(L, n, j):
    return C(L - 1, n) ** 2 * (-1) ** n * C(-L - 1, n) * C(L - 1, n + j) ** 2 * (-1) ** (j - 1) * C(-L - 1, j - 1)

def Kker(L, n, w=lambda j: 1):
    if n >= L:
        return 0
    return sum(w(j) * Psi(L, n, j) for j in range(0, L - n))

def Stilde(N, k, j):
    return C(N - 1, k) ** 2 * C(N + k - 1, k) * C(N - 1, k + j) ** 2 * C(N + j - 1, j)

# ============================================================================ I. Lemma 3.3
def section_I():
    out("\n=== I. Lemma 3.3: exact factorizations ===")
    for p in (5, 7):
        for m in (1, 2):
            for r in (1, 2):
                N = m * p ** r
                ok1 = all(Fr(Stilde(N, k, j)) == Fr(N, N + k) * Psi(N, k, j) for k in range(0, N + 2) for j in range(0, N + 2))
                ok2 = all(Fr(Psi(N, n, j)) == Fr(N, j) * Xihat(N, n, j) for n in range(0, N + 2) for j in range(1, N + 2))
                record(f"L3.3 S~(N;k,j) = N/(N+k) Psi_r(k,j), p={p} m={m} r={r}", ok1)
                record(f"L3.3 Psi_u(n,j) = (L/j) Xihat_u(n,j) (all j>=1), p={p} m={m} r={r}", ok2)
                ok3 = all(Fr(Stilde(N, k, j)) == Fr(N * N, k * j) * Xihat(N, k, j) - Fr(N ** 3, k * k * j) / (1 + Fr(N, k)) * Xihat(N, k, j)
                          for k in range(1, N + 1) for j in range(1, N + 1) if k % p and j % p)
                record(f"Section 6 exact decomposition of S~ for p∤k,p∤j, p={p} m={m} r={r}", ok3)

# ============================================================================ J. Lemma 3.4
def section_J():
    out("\n=== J. Lemma 3.4 (a),(b),(c),(d) for p in {5,7}, m in {1,2}, u in {1,2} ===")
    for p in (5, 7):
        h = harm(p)
        for m in (1, 2):
            for u in (1, 2):
                L, Lp = m * p ** u, m * p ** (u - 1)
                # (a)
                ok_uns = ok_sc = True; w_uns = w_sc = INF
                for q in range(0, L + p):
                    for j in range(0, L + p):
                        if j % p:
                            v = vp_int(Psi(L, q, j), p); w_uns = min(w_uns, v - u)
                            if v < u: ok_uns = False
                        else:
                            v = vp_int(Psi(L, q, j) - Psi(Lp, q // p, j // p), p); w_sc = min(w_sc, v - u)
                            if v < u: ok_sc = False
                record(f"L3.4(a) unscaled Psi_u(q,j)==0 mod p^u, p={p} m={m} u={u}", ok_uns, f"min slack {fmt_v(w_uns)}")
                record(f"L3.4(a) scaled Psi_u(q,pj1)==Psi_(u-1)([q/p],j1) mod p^u, p={p} m={m} u={u}", ok_sc, f"min slack {fmt_v(w_sc)}")
                okK = True; wK = INF
                for q in range(0, L + p):
                    v = vp_int(Kker(L, q) - Kker(Lp, q // p), p); wK = min(wK, v - u)
                    if v < u: okK = False
                record(f"L3.4(a) tower K_u(q)==K_(u-1)([q/p]) mod p^u, p={p} m={m} u={u}", okK, f"min slack {fmt_v(wK)}")
                # (b)
                okX = True; wX = INF
                for q in range(0, L + p):
                    for qp in range(0, L + p):
                        for d in (0, 1):
                            d1 = int((q % p) + (qp % p) + d >= p)
                            v = vp_int(Xi(L, d, q, qp) - Xi(Lp, d1, q // p, qp // p), p); wX = min(wX, v - u)
                            if v < u: okX = False
                record(f"L3.4(b) Xi^(delta) tower mod p^u, p={p} m={m} u={u}", okX, f"min slack {fmt_v(wX)}")
                okXh = True; wXh = INF
                for n in range(0, L + p):
                    for j in range(1, L + p):
                        if j % p == 0:
                            continue
                        d = int((n % p) + (j % p) >= p)
                        v = vp_int(Xihat(L, n, j) - Xi(Lp, d, n // p, j // p), p); wXh = min(wXh, v - u)
                        if v < u: okXh = False
                record(f"L3.4(b) Xihat_u(n,j)==Xi^(delta)_(u-1) (p∤j) mod p^u, p={p} m={m} u={u}", okXh, f"min slack {fmt_v(wXh)}")
                # (c)
                for tt in (1, 2, 3):
                    okM = True; wM = INF
                    for q in range(0, L + p):
                        v = vp_int(Kker(L, q, lambda j, tt=tt: j ** tt), p); wM = min(wM, v - u)
                        if v < u: okM = False
                    record(f"L3.4(c) moment kernel K^[{tt}]_u(q)==0 mod p^u, p={p} m={m} u={u}", okM, f"min slack {fmt_v(wM)}")
                # (d)
                for d in (1, 2):
                    okH = True; wH = INF
                    for q in range(0, L + p):
                        lhs = sum((Psi(L, q, j) * h.Hp(p ** d * j) for j in range(0, max(L - q, 0))), Fr(0))
                        q1 = q // p
                        rhs = sum((Psi(Lp, q1, j1) * h.Hp(p ** (d + 1) * j1) for j1 in range(0, max(Lp - q1, 0))), Fr(0))
                        v = vp(lhs - rhs, p); wH = min(wH, v - u)
                        if v < u: okH = False
                    record(f"L3.4(d) harmonic kernel K~^({d})_u(q)==K~^({d+1})_(u-1)([q/p]) mod p^u, p={p} m={m} u={u}", okH, f"min slack {fmt_v(wH)}")

# ============================================================================ K. Lemma 3.5
def section_K():
    out("\n=== K. Lemma 3.5: exact factorization Psi_(u+1)(n,p j1) = Psi_u([n/p],j1) P_n^2 Pbar_n P_{n+pj1}^2 Pbar_{pj1}, and the mod p^{2u+2} model ===")
    for p in (5, 7):
        h = harm(p)
        for m in (1, 2):
            for u in (0, 1, 2):
                L, Lp = m * p ** (u + 1), m * p ** u
                if L > 700:
                    out(f"  (skipping p={p} m={m} u={u}: L={L} too large for the exhaustive Fraction check)")
                    continue
                # prefix products
                P = [Fr(1)]; Pb = [Fr(1)]
                for x in range(1, L + 1):
                    P.append(P[-1] * (1 - Fr(L, x)) if x % p else P[-1])
                    Pb.append(Pb[-1] * (1 + Fr(L, x)) if x % p else Pb[-1])
                ok_exact = True; ok_cong = True; w = INF; count = 0
                for n in range(0, L):
                    q = n // p
                    for j1 in range(0, Lp):
                        if n + p * j1 > L - 1:
                            # both sides vanish; check that too
                            if Psi(L, n, p * j1) != 0 or Psi(Lp, q, j1) != 0:
                                ok_exact = False
                            continue
                        count += 1
                        E = P[n] ** 2 * Pb[n] * P[n + p * j1] ** 2 * Pb[p * j1]
                        if Fr(Psi(L, n, p * j1)) != Psi(Lp, q, j1) * E:
                            ok_exact = False
                        rho = h.Hp(n) - h.Hp(p * j1) + 2 * h.Hp(n + p * j1)
                        diff = Psi(L, n, p * j1) - Psi(Lp, q, j1) * (1 - L * rho)
                        v = vp(diff, p); w = min(w, v - (2 * u + 2))
                        if v < 2 * u + 2:
                            ok_cong = False
                record(f"L3.5 exact factorization p={p} m={m} u={u} (L={L}, {count} nonzero pairs)", ok_exact)
                record(f"L3.5 congruence mod p^(2u+2) with rho = H'_n - H'_(pj1) + 2H'_(n+pj1), p={p} m={m} u={u}", ok_cong, f"min slack {fmt_v(w)}")

# ============================================================================ main
def main():
    t0 = time.time()
    out("Referee A: independent checks of Sections 0-3 of notes/A376462-shifted-congruence-proof.md")
    out(f"python {sys.version.split()[0]}; exact arithmetic (int / Fraction)")
    for sec in (section_A, section_B, section_C, section_D, section_E, section_F, section_G, section_H, section_I, section_J, section_K):
        t1 = time.time()
        sec()
        out(f"  ({sec.__name__}: {time.time()-t1:.1f}s)")
    out("\n=== SUMMARY ===")
    if FAILS:
        out(f"{len(FAILS)} FAILED checks:")
        for name, d in FAILS:
            out(f"  - {name} {d}")
    else:
        out("All recorded checks passed.")
    out(f"total time {time.time()-t0:.1f}s")
    os.makedirs(os.path.dirname(OUTPATH), exist_ok=True)
    with open(OUTPATH, 'w') as f:
        f.write('\n'.join(LINES) + '\n')
    print(f"\nwritten: {OUTPATH}")

if __name__ == '__main__':
    main()
