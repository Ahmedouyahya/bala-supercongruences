#!/usr/bin/env python3
# Independent re-review of notes/A370092-periodicity-proof.md, part 3: the Amice/Colmez step for p=2, h=1.
# Colmez, Th. I.4.7: { floor(n/p^h)! C(x,n) } is an orthonormal basis of LA_h(Z_p, L); with Rem. I.4.4 the valuation
# v_LA_h(phi) = min over classes a of min_k v_p(a_k(phi,a)), a_k being the coefficients in the variable (x-a)/p^h.
# Tests: (A) the basis elements floor(k/2)! C(x,k) lie in the unit ball (integral t-coefficients on both classes), and
#        many C(x,k) without the factorial do not; (B) random f with Z-polynomial local expansions in t=(x-a)/2 satisfy
#        v2(a_k(f)) >= v2(floor(k/2)!), with slack 0 attained; (C) controls: with half-integral t-coefficients the bound
#        fails, with integral coefficients in (x-a) it holds with larger slack; (D) the three specific functions of the note.
# Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_amice.py
import os, random
from math import comb, factorial
from fractions import Fraction as Fr

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_amice.txt")
lines = []
npass = nfail = 0
def rec(ok, msg):
    global npass, nfail
    if ok: npass += 1
    else: nfail += 1
    lines.append(("PASS " if ok else "FAIL ") + msg)
def info(msg): lines.append("INFO " + msg)
INF = 10 ** 9
def v2(x):
    x = Fr(x)
    if x == 0: return INF
    n, d = abs(x.numerator), x.denominator; v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def v2f(j): return j - bin(j).count("1")
def mahler(fvals, k):  # a_k(f) = sum_j (-1)^(k-j) C(k,j) f(j)
    return sum((-1) ** (k - j) * comb(k, j) * fvals[j] for j in range(k + 1))

def polymul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] += x * y
    return r
def binom_poly_local(k, a):
    """coefficients in t of C(a+2t, k) = prod_{i<k} (a+2t-i) / k!"""
    p = [Fr(1)]
    for i in range(k): p = polymul(p, [Fr(a - i), Fr(2)])
    return [x / factorial(k) for x in p]

# ---- (A) unit-ball membership of the Amice basis (Colmez Lemme I.4.9 (i) for p=2,h=1), and failure without the factorial
KA = 70
ok = True; nonint_without = []
for k in range(KA + 1):
    for a in (0, 1):
        co = binom_poly_local(k, a)
        if min(v2(x) for x in co) + v2f(k // 2) < 0: ok = False
    if min(min(v2(x) for x in binom_poly_local(k, a)) for a in (0, 1)) < 0: nonint_without.append(k)
rec(ok, f"floor(k/2)! C(x,k) has Z_2-integral coefficients in t=(x-a)/2 on both classes, k<={KA}")
info(f"k<={KA} for which C(x,k) alone is NOT in the unit ball of LA_1: {nonint_without[:20]}... (count {len(nonint_without)})")
# exactness: v_LA1( floor(k/2)! C(x,k) ) == 0 (orthonormal => valuation exactly 0)
exact0 = all(min(min(v2(x) for x in binom_poly_local(k, a)) for a in (0, 1)) + v2f(k // 2) == 0 for k in range(KA + 1))
rec(exact0, f"v_LA1(floor(k/2)! C(x,k)) = 0 exactly for k<={KA}")

# ---- (B) random functions with Z-polynomial local expansions in t
random.seed(20261015)
KB = 60
worst = INF; where = None; viol = []
for trial in range(400):
    deg = random.randint(0, 10)
    c0 = [random.randint(-99, 99) for _ in range(deg + 1)]
    c1 = [random.randint(-99, 99) for _ in range(deg + 1)]
    def f(j):
        a = j % 2; t = (j - a) // 2; cs = c1 if a else c0
        return sum(cc * t ** i for i, cc in enumerate(cs))
    vals = [f(j) for j in range(KB + 1)]
    for k in range(KB + 1):
        ak = mahler(vals, k)
        if ak == 0: continue
        s = v2(ak) - v2f(k // 2)
        if s < 0: viol.append((trial, k, s))
        if s < worst: worst = s; where = (trial, k)
rec(not viol, f"(B) 400 random f (deg<=10, integer t-coefficients): v2(a_k(f)) >= v2(floor(k/2)!) for k<={KB}; violations {viol[:5]}")
rec(worst == 0, f"(B) minimum slack = {worst} at (trial,k)={where} (bound is attained)")
# structured functions: indicator of a class times t^i (the e_{1,n} of Colmez Lemme I.4.5)
viol = []; slack0 = 0
for a in (0, 1):
    for i in range(0, 25):
        vals = [((j - a) // 2) ** i if j % 2 == a else 0 for j in range(KB + 1)]
        for k in range(KB + 1):
            ak = mahler(vals, k)
            if ak == 0: continue
            s = v2(ak) - v2f(k // 2)
            if s < 0: viol.append((a, i, k, s))
            if s == 0: slack0 += 1
rec(not viol, f"(B) e_{{1,n}}-type functions 1_(a+2Z2)(x) t^i (i<25): bound holds for k<={KB}; violations {viol[:5]}; #slack-0 pairs {slack0}")

# ---- (C) controls on the normalisation
random.seed(7)
viol_half = 0; tot = 0
for trial in range(100):
    deg = random.randint(1, 8)
    c0 = [Fr(random.randint(-99, 99), 2) for _ in range(deg + 1)]
    c1 = [Fr(random.randint(-99, 99), 2) for _ in range(deg + 1)]
    def f(j):
        a = j % 2; t = (j - a) // 2; cs = c1 if a else c0
        return sum(cc * t ** i for i, cc in enumerate(cs))
    vals = [f(j) for j in range(41)]
    for k in range(41):
        ak = mahler(vals, k)
        if ak == 0: continue
        tot += 1
        if v2(ak) - v2f(k // 2) < 0: viol_half += 1
rec(viol_half > 0, f"(C) control: with t-coefficients in (1/2)Z the bound v2(a_k) >= v2(floor(k/2)!) FAILS in {viol_half}/{tot} cases (normalisation matters)")
random.seed(8)
worst_x = INF
for trial in range(100):
    deg = random.randint(1, 8)
    c0 = [random.randint(-99, 99) for _ in range(deg + 1)]
    c1 = [random.randint(-99, 99) for _ in range(deg + 1)]
    def f(j):  # integral coefficients in s = x - a  (stronger hypothesis)
        a = j % 2; s = j - a; cs = c1 if a else c0
        return sum(cc * s ** i for i, cc in enumerate(cs))
    vals = [f(j) for j in range(41)]
    for k in range(1, 41):
        ak = mahler(vals, k)
        if ak == 0: continue
        worst_x = min(worst_x, v2(ak) - v2f(k // 2))
rec(worst_x >= 0, f"(C) control: integral coefficients in (x-a) (stronger) => bound holds, min slack {worst_x}")

# ---- (D) the specific functions in the note
def Fx(n, m, x): return x ** n * (x ** (2 ** m) - 1)
ok_f = ok_E = ok_S2 = True; minsl = {"f": INF, "E": INF, "S2": INF}
for m in range(2, 7):
    P = 2 ** m
    for n in range(m + 1, m + 10):
        vals = [Fx(n, m, j) for j in range(61)]
        valsE = [Fx(n, m, j) if j % 2 == 0 else 0 for j in range(61)]
        def Rm(t): return sum(Fr(comb(P, i) * 2 ** i, 2 ** (m + 2)) * t ** i for i in range(3, P + 1))
        valsS2 = [0 if j % 2 == 0 else j ** n * Rm((j - 1) // 2) for j in range(61)]
        for k in range(61):
            ak = mahler(vals, k)
            if ak:
                s = v2(ak) - (m + 1) - v2f(k // 2); minsl["f"] = min(minsl["f"], s)
                if s < 0: ok_f = False
            ek = mahler(valsE, k)
            if ek:
                s = v2(ek) - n - v2f(k // 2); minsl["E"] = min(minsl["E"], s)
                if s < 0: ok_E = False
            sk = mahler(valsS2, k)
            if sk:
                s = v2(sk) - v2f(k // 2); minsl["S2"] = min(minsl["S2"], s)
                if s < 0: ok_S2 = False
rec(ok_f, f"(D) f=2^-(m+1)F, n>=m+1: v2(a_k(F)) >= m+1+v2(floor(k/2)!) for k<=60, m=2..6; min slack {minsl['f']}")
rec(ok_E, f"(D) even part F*1_(2Z2): v2(E_k) >= n + v2(floor(k/2)!) ; min slack {minsl['E']}")
rec(ok_S2, f"(D) S_2 function: v2(S_2) >= v2(floor(k/2)!) ; min slack {minsl['S2']}")
# (E) Mahler coefficients of a finite combination sum beta_k floor(k/2)! C(x,k) are beta_k floor(k/2)!
random.seed(3)
beta = [random.randint(-50, 50) for _ in range(30)]
vals = [sum(beta[k] * factorial(k // 2) * comb(x, k) for k in range(30)) for x in range(60)]
rec(all(mahler(vals, k) == (beta[k] * factorial(k // 2) if k < 30 else 0) for k in range(60)), "(E) a_k(sum beta_l floor(l/2)! C(x,l)) = beta_k floor(k/2)!")

lines.append(f"TOTAL: {npass} pass, {nfail} fail")
print("\n".join(lines))
with open(OUT, "w") as fh: fh.write("\n".join(lines) + "\n")
