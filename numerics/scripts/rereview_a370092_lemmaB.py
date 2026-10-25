#!/usr/bin/env python3
# Independent re-review of notes/A370092-periodicity-proof.md, part 2:
# Lemma B, bound (2), local expansions, the decomposition b_k = E_k + 2^{m+1} S_1 + 2^{m+2} S_2,
# the exceptional set {3,6,7,15}, the finite reduction for those k, and the by-hand formulas.
# All arithmetic exact.  Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_lemmaB.py
import os
from math import comb, factorial, log2
from fractions import Fraction as Fr

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_lemmaB.txt")
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
    if x == 0: return INF
    x = abs(int(x)); v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def v2f(j): return j - bin(j).count("1")      # v2(j!)
def bk(k, n, P): return sum((-1) ** (k - j) * comb(k, j) * j ** n * (j ** P - 1) for j in range(k + 1))

# ---------- (a) Lemma B directly: v2(b_k(n,2^m)) >= m+1+floor(k/3), n >= m+2
KMAX, NSPAN = 60, 100
viol = []; worst = {}
for m in range(2, 9):
    P = 2 ** m
    jP1 = [j ** P - 1 for j in range(KMAX + 1)]
    pw = [j ** (m + 2) for j in range(KMAX + 1)]
    for n in range(m + 2, m + 2 + NSPAN):
        for k in range(0, KMAX + 1):
            b = sum((-1) ** (k - j) * comb(k, j) * pw[j] * jP1[j] for j in range(k + 1))
            v = v2(b); need = m + 1 + k // 3
            if v < need: viol.append((m, k, n, v, need))
            if v < INF: worst[k] = min(worst.get(k, INF), v - need)
        pw = [pw[j] * j for j in range(KMAX + 1)]
rec(not viol, f"Lemma B: m=2..8, k<={KMAX}, m+2<=n<m+2+{NSPAN}: violations {viol[:8]}")
info("Lemma B slack min over (m,n) per k=0..40: " + str([worst.get(k) for k in range(41)]))
info("k<=60 with Lemma B slack 0: " + str([k for k in range(KMAX + 1) if worst.get(k) == 0]))
# profile claimed in the note: min over n of v2(b_k) - m independent of m, = 2,4,2,3,3,6,5,6,6,8 for k=3..12
prof = {}
for m in (2, 3, 5, 8):
    P = 2 ** m
    prof[m] = [min(v2(bk(k, n, P)) for n in range(m + 2, m + 2 + 64)) - m for k in range(3, 13)]
rec(all(prof[m] == [2, 4, 2, 3, 3, 6, 5, 6, 6, 8] for m in prof), f"NOTE'S PARENTHETICAL (Lemma B): 'the minimum over n of v2(b_k)-m is independent of m: 2,4,2,3,3,6,5,6,6,8 for k=3..12'; measured with n ranging over m+2..m+65: {prof}")
info("the committed file lemmaB_stirling_2adic.txt took the minimum over n in [40,200] only (m=5,8), which excludes the n=m+2 minimum at k=4 (v2(b_4(m+2,2^m)) = m+3 for every m)")

# n = m+2 exactly, larger m
viol = []
for m in range(2, 13):
    P = 2 ** m; n = m + 2
    for k in range(0, 45):
        v = v2(bk(k, n, P))
        if v < m + 1 + k // 3: viol.append((m, k, v))
rec(not viol, f"Lemma B at n = m+2 exactly, m=2..12, k<45: violations {viol}")
# failure for some k at EVERY n <= m+1 (note's claim); which k
fail_at = {}
for m in range(2, 9):
    P = 2 ** m
    for n in range(0, m + 2):
        ks = [k for k in range(0, 30) if v2(bk(k, n, P)) < m + 1 + k // 3]
        fail_at[(m, n)] = ks
rec(all(fail_at[(m, n)] for m in range(2, 9) for n in range(0, m + 2)), "Lemma B fails for some k at every n <= m+1 (m=2..8)")
rec(all(3 in fail_at[(m, n)] for m in range(2, 9) for n in range(0, m + 2)), "in particular k=3 fails at every n <= m+1")
info("k<30 failing Lemma B at n=m+1, for m=2..8: " + str({m: fail_at[(m, m + 1)] for m in range(2, 9)}))
info("k<30 failing Lemma B at n=m,   for m=2..8: " + str({m: fail_at[(m, m)] for m in range(2, 9)}))

# ---------- (b) bound (2): v2(b_k) >= m+1+v2(floor(k/2)!) for n >= m+1
viol = []; w2 = INF; wat = None
for m in range(2, 9):
    P = 2 ** m
    for n in range(m + 1, m + 1 + 60):
        for k in range(0, 50):
            v = v2(bk(k, n, P)); need = m + 1 + v2f(k // 2)
            if v < need: viol.append((m, k, n, v, need))
            elif v < INF and v - need < w2: w2 = v - need; wat = (m, k, n)
rec(not viol, f"bound (2) for n>=m+1, m=2..8, k<50: violations {viol[:8]}; min slack {w2} at (m,k,n)={wat}")
fails_at_m = [(m, k) for m in range(2, 7) for k in range(0, 30) if v2(bk(k, m, 2 ** m)) < m + 1 + v2f(k // 2)]
info("bound (2) at n = m (outside its hypothesis): failing (m,k) = " + str(fails_at_m[:12]) + " (so n>=m+1 is needed there)")

# ---------- (c) exceptional set and the analytic tail
exc = [k for k in range(0, 5000) if v2f(k // 2) < k // 3]
rec(exc == [3, 6, 7, 15], f"k<5000 with v2(floor(k/2)!) < floor(k/3): {exc}")
rec(all(v2f(k // 2) + 1 >= k // 3 for k in range(0, 5000)), "v2(floor(k/2)!) + 1 >= floor(k/3) for all k<5000")
rec([v2f(k // 2) + 1 for k in (3, 6, 7, 15)] == [1, 2, 2, 5] and [k // 3 for k in (3, 6, 7, 15)] == [1, 2, 2, 5], "for k in {3,6,7,15}: v2(floor(k/2)!)+1 = floor(k/3) = 1,2,2,5")
rec(all(v2f(k // 2) >= (k // 2) - log2(k) - 1 for k in range(1, 20000)), "v2(floor(k/2)!) >= floor(k/2) - log2(k) - 1, k<20000")
rec(all((k // 2) - log2(k) - 1 > k / 3 for k in range(401, 20000)), "floor(k/2) - log2(k) - 1 > k/3 for 400<k<20000")
info("smallest k from which floor(k/2)-log2(k)-1 > k/3 holds onward (k<1000): " + str(min(k0 for k0 in range(1, 1000) if all((k // 2) - log2(k) - 1 > k / 3 for k in range(k0, 1000)))))

# ---------- (d) local expansions on the classes mod 2 (normalised variable t = (x-a)/2)
def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] += x * y
    return r
def polypow(p, e):
    r = [1]
    for _ in range(e): r = polymul(r, p)
    return r
def F_odd(n, m):   # F(1+2t) as polynomial in t
    P = 2 ** m
    q = polypow([1, 2], P); q[0] -= 1
    return polymul(polypow([1, 2], n), q)
def F_even(n, m):  # F(2t)
    P = 2 ** m
    q = polypow([0, 2], P); q[0] -= 1
    return polymul(polypow([0, 2], n), q)
ok_even = ok_odd = ok_odd_exact = True
for m in range(2, 7):
    for n in range(0, m + 8):
        ce = [v2(x) for x in F_even(n, m) if x]
        co = [v2(x) for x in F_odd(n, m) if x]
        if min(ce) < n: ok_even = False
        if min(co) < m + 1: ok_odd = False
        if min(co) != m + 1: ok_odd_exact = False
rec(ok_even, "F(2t) in 2^n Z[t] (m=2..6, n<m+8)")
rec(ok_odd, "F(1+2t) in 2^(m+1) Z[t] (m=2..6, n<m+8)")
rec(ok_odd_exact, "min valuation of the coefficients of F(1+2t) is exactly m+1 (so v_LA1(2^-(m+1)F) = min(n-m-1,0) exactly)")
# Kummer and the coefficient valuations of (1+2t)^(2^m) - 1
ok1 = ok2 = ok3 = True
for m in range(1, 11):
    P = 2 ** m
    for i in range(1, P + 1):
        if v2(comb(P, i)) != m - v2(i): ok1 = False
        v = m - v2(i) + i
        if v < m + 1: ok2 = False
        if (v == m + 1) != (i in (1, 2)): ok3 = False
        if i >= 3 and v < m + 2: ok3 = False
rec(ok1, "v2(C(2^m,i)) = m - v2(i), 1<=i<=2^m, m<=10")
rec(ok2 and ok3, "v2(C(2^m,i) 2^i) = m - v2(i) + i >= m+1, equality iff i in {1,2}, >= m+2 for i>=3")
# R_m(t) integral and the identity (1+2t)^P - 1 = 2^{m+1}[t + (P-1)t^2] + 2^{m+2} R_m(t)
def R_m_coeffs(m):
    P = 2 ** m
    return [Fr(comb(P, i) * 2 ** i, 2 ** (m + 2)) for i in range(0, P + 1)]  # i<3 entries are zero after subtraction below
ok = True
for m in range(2, 9):
    P = 2 ** m
    lhs = polypow([1, 2], P); lhs[0] -= 1
    R = [Fr(0), Fr(0), Fr(0)] + [Fr(comb(P, i) * 2 ** (i - m - 2)) if i >= m + 2 else Fr(comb(P, i), 2 ** (m + 2 - i)) for i in range(3, P + 1)]
    if not all(x.denominator == 1 for x in R): ok = False
    rhs = [Fr(0)] * (P + 1)
    rhs[1] += 2 ** (m + 1); rhs[2] += 2 ** (m + 1) * (P - 1)
    for i in range(P + 1): rhs[i] += 2 ** (m + 2) * R[i]
    if [Fr(x) for x in lhs] != rhs: ok = False
    if not all(v2(x.numerator) == i - 2 - v2(i) for i, x in enumerate(R) if i >= 3): ok = False
rec(ok, "R_m(t) has integer coefficients with v2 = i-2-v2(i), and (1+2t)^(2^m)-1 = 2^(m+1)[t+(2^m-1)t^2] + 2^(m+2) R_m(t), m=2..8")

# ---------- (e) decomposition b_k = E_k + 2^{m+1} S_1 + 2^{m+2} S_2 (exact), all n>=0
def E_k(k, n, m):
    P = 2 ** m
    return sum((-1) ** (k - j) * comb(k, j) * j ** n * (j ** P - 1) for j in range(0, k + 1, 2))
def S_1(k, n, m):
    return sum((-1) ** (k - 1 - 2 * t) * comb(k, 2 * t + 1) * (1 + 2 * t) ** n * t * (1 + (2 ** m - 1) * t) for t in range((k - 1) // 2 + 1)) if k >= 1 else 0
def R_m_eval(m, t):
    P = 2 ** m
    return sum(Fr(comb(P, i) * 2 ** i, 2 ** (m + 2)) * t ** i for i in range(3, P + 1))
def S_2(k, n, m):
    return sum((-1) ** (k - 1 - 2 * t) * comb(k, 2 * t + 1) * (1 + 2 * t) ** n * R_m_eval(m, t) for t in range((k - 1) // 2 + 1)) if k >= 1 else 0
ok = True; cnt = 0; bad = []
for m in range(2, 7):
    for k in list(range(0, 20)) + [15]:
        for n in list(range(0, m + 12)):
            cnt += 1
            s2 = S_2(k, n, m)
            if Fr(s2).denominator != 1: ok = False; bad.append(("S2 non-integer", m, k, n))
            if E_k(k, n, m) + 2 ** (m + 1) * S_1(k, n, m) + 2 ** (m + 2) * s2 != bk(k, n, 2 ** m): ok = False; bad.append((m, k, n))
rec(ok, f"b_k = E_k + 2^(m+1) S_1 + 2^(m+2) S_2 exactly, {cnt} cases (m=2..6, k<20, 0<=n<m+12), bad {bad[:5]}")

# bounds for the parts: v2(E_k) >= n + v2(floor(k/2)!) (all n>=0), v2(S_2) >= v2(floor(k/2)!) (all n>=0)
wE = wS2 = INF; vE = vS2 = []
for m in range(2, 7):
    for k in range(0, 36):
        for n in range(0, m + 14):
            e = E_k(k, n, m); s2 = int(S_2(k, n, m))
            if e:
                s = v2(e) - (n + v2f(k // 2)); wE = min(wE, s)
                if s < 0: vE.append((m, k, n))
            if s2:
                s = v2(s2) - v2f(k // 2); wS2 = min(wS2, s)
                if s < 0: vS2.append((m, k, n))
rec(not vE, f"v2(E_k) >= n + v2(floor(k/2)!) for all n>=0 (m=2..6, k<36): min slack {wE}, violations {vE[:5]}")
rec(not vS2, f"v2(S_2) >= v2(floor(k/2)!) for all n>=0 (m=2..6, k<36): min slack {wS2}, violations {vS2[:5]}")
# consequence used in the note: for exceptional k and n>=m+2, E_k and 2^{m+2}S_2 are 0 mod 2^{m+1+floor(k/3)}
ok = True
for m in range(2, 8):
    for k in (3, 6, 7, 15):
        for n in range(m + 2, m + 2 + 30):
            d = m + 1 + k // 3
            if E_k(k, n, m) % 2 ** d or (2 ** (m + 2) * int(S_2(k, n, m))) % 2 ** d: ok = False
rec(ok, "exceptional k, n>=m+2: E_k == 0 and 2^(m+2) S_2 == 0 mod 2^(m+1+floor(k/3)) (m=2..7, 30 n each)")

# ---------- (f) S_1 for the exceptional k: direct and the finite reduction
viol = []; mins = {}
for k, d in ((3, 1), (6, 2), (7, 2), (15, 5)):
    mn = INF
    for m in range(2, 15):
        for n in range(0, 200):           # all n >= 0, not only n >= m+2
            v = v2(S_1(k, n, m)); mn = min(mn, v)
            if v < d: viol.append((k, m, n, v))
    mins[k] = mn
rec(not viol, f"v2(S_1) >= floor(k/3) for k in (3,6,7,15), ALL n in [0,200), m=2..14: violations {viol[:5]}; min v2(S_1) per k = {mins}")
# invariance claims behind the finite reduction (mod 2^d dependence on n mod lambda(2^d) and on (2^m-1) mod 2^d)
lam = {1: 1, 2: 2, 5: 8}
ok_n = ok_m = True
for k, d in ((3, 1), (6, 2), (7, 2), (15, 5)):
    L = lam[d]; md = 2 ** d
    for m in range(2, 13):
        for n in range(0, 60):
            if (S_1(k, n + L, m) - S_1(k, n, m)) % md: ok_n = False
    for m in range(2, 13):
        for m2 in range(2, 13):
            if (2 ** m - 1) % md == (2 ** m2 - 1) % md:
                for n in range(0, 20):
                    if (S_1(k, n, m) - S_1(k, n, m2)) % md: ok_m = False
rec(ok_n, "S_1 mod 2^d is periodic in n with period lambda(2^d) (= 1,2,2,8), m=2..12, n<60")
rec(ok_m, "S_1 mod 2^d depends on m only through (2^m - 1) mod 2^d (m,m' in 2..12)")
# the finite case set the note describes (m = 2..d plus one m>=d, n over a full period starting at m+2) covers the claim; enumerate it
ok = True; cases = 0
for k, d in ((3, 1), (6, 2), (7, 2), (15, 5)):
    L = lam[d]
    for m in list(range(2, d + 1)) + [max(d, 2) + 1]:
        for n in range(m + 2, m + 2 + L):
            cases += 1
            if v2(S_1(k, n, m)) < d: ok = False
rec(ok, f"the note's finite case set (m=2..d plus one m>=d, one full n-period from m+2): {cases} cases, all v2(S_1) >= d")
# by-hand formulas
ok3 = all(S_1(3, n, m) == 2 ** m * 3 ** n for m in range(2, 10) for n in range(0, 40))
ok6 = all(S_1(6, n, m) == -20 * 3 ** n * 2 ** m - 6 * 5 ** n * 2 * (1 + 2 * (2 ** m - 1)) for m in range(2, 10) for n in range(0, 40))
ok7 = all(S_1(7, n, m) == 35 * 3 ** n * 2 ** m + 21 * 5 ** n * 2 * (2 ** (m + 1) - 1) + 7 ** n * 3 * (3 * 2 ** m - 2) for m in range(2, 10) for n in range(0, 40))
rec(ok3, "by hand k=3: S_1 = 2^m 3^n")
rec(ok6, "by hand k=6: S_1 = -20*3^n*2^m - 6*5^n*2*(1+2(2^m-1))")
rec(ok7, "by hand k=7: S_1 = 35*3^n*2^m + 21*5^n*2*(2^(m+1)-1) + 7^n*3*(3*2^m-2)")
rec(all((21 * 5 ** n + 3 * 7 ** n) % 2 == 0 for n in range(0, 50)), "21*5^n + 3*7^n is even")
rec(all((-2 * (21 * 5 ** n + 3 * 7 ** n) - S_1(7, n, m)) % 4 == 0 for m in range(2, 8) for n in range(0, 30)), "k=7: S_1 == -2(21*5^n+3*7^n) (mod 4)")
# b_3 closed form and its exact valuation
okb3 = all(bk(3, n, 2 ** m) == 3 ** n * (3 ** (2 ** m) - 1) - 3 * 2 ** n * (2 ** (2 ** m) - 1) for m in range(2, 9) for n in range(1, 40))
rec(okb3, "b_3 = 3^n(3^(2^m)-1) - 3*2^n(2^(2^m)-1) for n>=1 (at n=0 the j=0 term contributes 0^0=1; the note uses the formula for n>=m+2)")
rec(all(v2(bk(3, n, 2 ** m)) == m + 2 for m in range(2, 10) for n in range(m + 3, m + 40)), "v2(b_3) = m+2 exactly for n >= m+3")
info("v2(b_3) at n=m+2, m=2..9: " + str([v2(bk(3, m + 2, 2 ** m)) for m in range(2, 10)]) + " (note says only >= m+2)")
rec(all(v2(bk(3, n, 2 ** m)) == n for m in range(2, 10) for n in range(1, m + 2)), "v2(b_3) = n < m+2 for 1 <= n <= m+1 (Lemma B start n>=m+2 is sharp)")
rec(all(v2(3 ** (2 ** m) - 1) == m + 2 for m in range(1, 12)), "v2(3^(2^m)-1) = m+2")

lines.append(f"TOTAL: {npass} pass, {nfail} fail")
print("\n".join(lines))
with open(OUT, "w") as fh: fh.write("\n".join(lines) + "\n")
