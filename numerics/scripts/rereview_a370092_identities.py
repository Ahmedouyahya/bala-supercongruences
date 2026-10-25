#!/usr/bin/env python3
# Independent re-review of notes/A370092-periodicity-proof.md, part 1:
# exact identities of sections 0-1 ((e.g.f., recurrence, G(u), (1), (P1), (P2), (P3)) and the alpha<=2 clause of Prop. 2.
# All arithmetic exact (int / Fraction).  Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_identities.py
import os
from fractions import Fraction as Fr
from math import comb, factorial

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_identities.txt")
lines = []
npass = nfail = 0
def rec(ok, msg):
    global npass, nfail
    if ok: npass += 1
    else: nfail += 1
    lines.append(("PASS " if ok else "FAIL ") + msg)
def info(msg): lines.append("INFO " + msg)

def v2(x):
    x = Fr(x)
    if x == 0: return None
    n, d = abs(x.numerator), x.denominator; v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v

N = 200
# ---- a(n) by the recurrence displayed in section 0
a = [Fr(1)]
for n in range(1, N + 1):
    s = sum((1 - (-1) ** j - (-2) ** j) * comb(n, j) * a[n - j] for j in range(1, n + 1))
    a.append(Fr((-1) ** n) + Fr(s, 2))
rec(all(x.denominator == 1 for x in a), f"section-0 recurrence gives integers for n<={N}")
a = [int(x) for x in a]
rec(a[:7] == [1, 1, 3, 16, 105, 856, 8433], f"first values {a[:7]} == 1,1,3,16,105,856,8433")

# ---- e.g.f. check: Taylor coefficients of 2e^x/(1+e^x+e^{2x}-e^{3x})
M = 60
def expser(c):
    return [Fr(c ** i, factorial(i)) for i in range(M + 1)]
def add(*ss): return [sum(t) for t in zip(*ss)]
def scal(c, s): return [c * x for x in s]
def mul(s, t):
    r = [Fr(0)] * (M + 1)
    for i, x in enumerate(s):
        if x == 0: continue
        for j in range(M + 1 - i): r[i + j] += x * t[j]
    return r
def inv(s):
    r = [Fr(0)] * (M + 1); r[0] = 1 / s[0]
    for n in range(1, M + 1):
        r[n] = -sum(s[i] * r[n - i] for i in range(1, n + 1)) / s[0]
    return r
one = [Fr(1)] + [Fr(0)] * M
den = add(one, expser(1), expser(2), scal(-1, expser(3)))
F = mul(scal(2, expser(1)), inv(den))
rec(all(F[n] * factorial(n) == a[n] for n in range(M + 1)), f"e.g.f. 2e^x/(1+e^x+e^2x-e^3x) reproduces a(n), n<={M}")
# recurrence read off directly from the e.g.f.: 2a(n) + sum_{j>=1} C(n,j)(1+2^j-3^j) a(n-j) = 2
b = [1]
for n in range(1, N + 1):
    s = sum((1 + 2 ** j - 3 ** j) * comb(n, j) * b[n - j] for j in range(1, n + 1))
    assert s % 2 == 0
    b.append(1 - s // 2)
rec(b == a, "e.g.f.-derived recurrence a(n)=1-(1/2)sum(1+2^j-3^j)C(n,j)a(n-j) agrees with the note's recurrence")

# ---- u = e^x - 1: 1 + e^x + e^{2x} - e^{3x} = 2 - 2u^2 - u^3
poly = [0] * 4
for cc, p in ((1, 0), (1, 1), (1, 2), (-1, 3)):
    for i in range(p + 1): poly[i] += cc * comb(p, i)
rec(poly == [2, 0, -2, -1], f"1+(1+u)+(1+u)^2-(1+u)^3 = {poly} (i.e. 2 - 2u^2 - u^3)")

# ---- G(u) = (1+u)/(1-u^2-u^3/2): series division vs recurrence 2g_k = 2g_{k-2} + g_{k-3}
K = 400
den_u = [Fr(1), Fr(0), Fr(-1), Fr(-1, 2)] + [Fr(0)] * (K - 3)
num_u = [Fr(1), Fr(1)] + [Fr(0)] * (K - 1)
gdiv = [Fr(0)] * (K + 1)
for n in range(K + 1):
    gdiv[n] = num_u[n] - sum(den_u[i] * gdiv[n - i] for i in range(1, n + 1))
g = [Fr(1), Fr(1), Fr(1)]
for k in range(3, K + 1): g.append(g[k - 2] + g[k - 3] / 2)
rec(g == gdiv, f"g_k by series division == g_k by recurrence 2g_k=2g_(k-2)+g_(k-3), k<={K}")
rec(g[:4] == [1, 1, 1, Fr(3, 2)], f"g_0..g_3 = {[str(x) for x in g[:4]]}")
rec(g[4] == Fr(3, 2) and g[5] == 2 and g[6] == Fr(9, 4) and g[7] == Fr(11, 4), f"g_4..g_7 = {[str(x) for x in g[4:8]]}")
# F(x) = G(e^x - 1): compose series
u = expser(1); u[0] -= 1
pw = [Fr(1)] + [Fr(0)] * M
Gcomp = [Fr(0)] * (M + 1)
for k in range(M + 1):
    Gcomp = add(Gcomp, scal(g[k], pw))
    pw = mul(pw, u)
rec(Gcomp == F, f"F(x) = G(e^x - 1) as power series, n<={M}")

# ---- identity (1): a(n) = sum_k c_k S(n,k), c_k = k! g_k
S = [[0] * (N + 1) for _ in range(N + 1)]; S[0][0] = 1
for n in range(1, N + 1):
    for k in range(1, n + 1): S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
c = [g[k] * factorial(k) for k in range(K + 1)]
rec(all(x.denominator == 1 for x in c), f"(P2) c_k = k! g_k is an integer for k<={K}")
c = [int(x) for x in c]
rec(all(a[n] == sum(c[k] * S[n][k] for k in range(n + 1)) for n in range(N + 1)), f"identity (1) a(n) = sum_k c_k S(n,k) for n<={N}")
rec(c[:8] == [1, 1, 2, 9, 36, 240, 1620, 13860], f"c_0..c_7 = {c[:8]}")
for k in (0, 1, 2, 3, 5, 8):
    s = [Fr(1)] + [Fr(0)] * M
    for _ in range(k): s = mul(s, u)
    rec(all(s[n] * factorial(n) == factorial(k) * S[n][k] for n in range(M + 1)), f"(e^x-1)^{k} = sum_n k! S(n,k) x^n/n!, n<={M}")

# ---- (P1) v2(g_k) >= -floor(k/3)
slack = [v2(g[k]) + k // 3 for k in range(K + 1)]
rec(all(s >= 0 for s in slack), f"(P1) v2(g_k) >= -floor(k/3) for k<={K}; min slack {min(slack)}")
info("(P1) k<40 with v2(g_k) = -floor(k/3) exactly: " + str([k for k in range(40) if slack[k] == 0]))
info("v2(g_k), k=0..30: " + str([v2(g[k]) for k in range(31)]))
rec(all((g[k].denominator & (g[k].denominator - 1)) == 0 for k in range(K + 1)), "g_k in Z[1/2] (all denominators powers of 2)")
rec(all(j - 2 * (-(-j // 3)) <= j // 3 for j in range(0, 2000)), "(P1) proof: j - 2*ceil(j/3) <= floor(j/3), j<2000")
ok = True
for mm in range(0, 60):
    for r in range(0, mm + 1):
        if r > (2 * mm + r) // 3: ok = False
rec(ok, "(P1) proof: r = j-2m <= floor(j/3) whenever 0<=r<=m (m<60)")
# direct check of the coefficient claim: [u^j](u^2+u^3/2)^m = C(m,r)/2^r, r=j-2m
ok = True
for mm in range(0, 12):
    p = [Fr(1)]
    base = [Fr(0), Fr(0), Fr(1), Fr(1, 2)]
    for _ in range(mm):
        q = [Fr(0)] * (len(p) + 3)
        for i, x in enumerate(p):
            for j2, y in enumerate(base): q[i + j2] += x * y
        p = q
    for j in range(len(p)):
        r = j - 2 * mm
        expect = Fr(comb(mm, r), 2 ** r) if 0 <= r <= mm else Fr(0)
        if p[j] != expect: ok = False
rec(ok, "(P1) proof: [u^j](u^2+u^3/2)^m = C(m,r)/2^r with r=j-2m, m<12")

# ---- (P2) valuation chain
def v2fact(k): return k - bin(k).count("1")
rec(all(v2fact(k) == v2(factorial(k)) for k in range(0, 300)), "v2(k!) = k - s_2(k), k<300")
rec(all(v2fact(k) >= k // 3 for k in range(0, 5000)), "(P2) v2(k!) >= floor(k/3), k<5000")
rec(all(k - (k.bit_length() - 1) - 1 >= k // 3 for k in range(16, 5000)), "(P2) k - floor(log2 k) - 1 >= floor(k/3) for 16<=k<5000")
info("(P2) k>=1 where that chain fails: " + str([k for k in range(1, 16) if k - (k.bit_length() - 1) - 1 < k // 3]) + " (empty => 'k>=16' is merely conservative)")
rec(all(v2fact(k) - k // 3 >= 2 for k in range(6, 5000)), "(P2) v2(k!) - floor(k/3) >= 2 for 6<=k<5000")
rec(all(k - (k.bit_length() - 1) - 1 - k // 3 >= 2 for k in range(12, 5000)), "(P2) chain gives >=2 for 12<=k<5000")
info("(P2) 6<=k<=11 where the chain does not give >=2: " + str([k for k in range(6, 12) if k - (k.bit_length() - 1) - 1 - k // 3 < 2]))
rec(all(v2(c[k]) >= 2 for k in range(4, K + 1)), f"v2(c_k) >= 2 for 4<=k<={K} (used in Prop. 2, alpha<=2)")
info("v2(c_k), k=0..12: " + str([v2(c[k]) for k in range(13)]))
rec(v2(c[4]) == 2 and v2(c[5]) == 4 and v2(c[6]) == 2 and v2(c[7]) == 2, "v2(c_4..c_7) = 2,4,2,2 (c_4=36, c_5=240)")

# ---- (P3) b_k(n,P) = k!(S(n+P,k)-S(n,k)) = sum_j (-1)^(k-j) C(k,j) j^n (j^P-1), with 0^0 = 1
def bk_formula(k, n, P): return sum((-1) ** (k - j) * comb(k, j) * j ** n * (j ** P - 1) for j in range(k + 1))
ok = True; cnt = 0; bad = []
for P in (1, 2, 3, 4, 8, 16):
    for n in range(0, 40):
        for k in range(0, n + P + 2):
            cnt += 1
            if factorial(k) * (S[n + P][k] - S[n][k]) != bk_formula(k, n, P): ok = False; bad.append((k, n, P))
rec(ok, f"(P3) b_k identity: {cnt} cases, P in (1,2,3,4,8,16), 0<=n<40, 0<=k<=n+P+1; mismatches {bad[:5]}")
ok = True
for P in (1, 2, 4, 6, 8, 16):
    for n in range(0, 60):
        if sum(g[k] * bk_formula(k, n, P) for k in range(0, n + P + 1)) != a[n + P] - a[n]: ok = False
rec(ok, "(P3) a(n+P) - a(n) = sum_k g_k b_k(n,P), P in (1,2,4,6,8,16), n<60")
rec(bk_formula(0, 0, 4) == -1 and bk_formula(0, 3, 4) == 0 and bk_formula(1, 0, 4) == 1 and bk_formula(1, 5, 4) == 0, "edge k=0,1: b_0(0,P)=-1, b_0(n>0)=0, b_1(0,P)=1, b_1(n>0)=0")
rec(all(bk_formula(2, n, 2 ** m) == 2 ** n * (2 ** (2 ** m) - 1) for n in range(1, 30) for m in range(2, 6)), "edge k=2: b_2(n,2^m) = 2^n (2^(2^m)-1) for n>=1")

# ---- Prop. 2, alpha <= 2 closed forms
rec(all(S[n][1] == 1 and S[n][2] == 2 ** (n - 1) - 1 and 2 * S[n][3] == 3 ** (n - 1) - 2 ** n + 1 for n in range(1, 120)), "S(n,1)=1, S(n,2)=2^(n-1)-1, S(n,3)=(3^(n-1)-2^n+1)/2 for 1<=n<120")
def lowpart(n): return Fr(1) + 2 * (2 ** (n - 1) - 1) + Fr(9 * (3 ** (n - 1) - 2 ** n + 1), 2)
rec(all(lowpart(n).denominator == 1 and (a[n] - lowpart(n)) % 4 == 0 for n in range(1, N + 1)), f"a(n) == 1 + 2(2^(n-1)-1) + 9(3^(n-1)-2^n+1)/2 (mod 4), 1<=n<={N}")
rec(all((lowpart(n) - (-1 + Fr(9, 2) * (3 ** (n - 1) + 1))) % 4 == 0 for n in range(3, 200)), "that expression == -1 + (9/2)(3^(n-1)+1) (mod 4) for n>=3")
info("n<3 where the last congruence fails: " + str([n for n in range(1, 3) if (lowpart(n) - (-1 + Fr(9, 2) * (3 ** (n - 1) + 1))) % 4 != 0]))
rec(all(((3 ** (n - 1) + 1) // 2) % 4 == (1 if n % 2 else 2) for n in range(1, 200)), "(3^(n-1)+1)/2 == 1 (n odd), 2 (n even) mod 4")
rec(all((a[n] % 4) == (0 if n % 2 else 1) for n in range(3, N + 1)), f"a(n) mod 4 == 0 (n odd), 1 (n even) for 3<=n<={N}")
info("a(n) mod 4 for n=0..8: " + str([a[n] % 4 for n in range(9)]) + "  (a(2)=3 mod 4 != a(4)=1 mod 4: start n>=3 of the mod-4 clause is sharp)")
rec(a[2] % 4 != a[4] % 4, "mod 4: a(2) != a(4) mod 4, so start n>=3 is sharp")
rec(all((a[n] % 2) == (0 if n % 2 else 1) for n in range(2, N + 1)), f"a(n) mod 2 == 0 (n odd), 1 (n even) for 2<=n<={N}")
rec(all((a[n] - (1 + (3 ** (n - 1) + 1) // 2)) % 2 == 0 for n in range(2, 200)), "a(n) == 1 + (3^(n-1)+1)/2 (mod 2) for n>=2")
rec(a[1] % 2 == 1 and a[3] % 2 == 0, "a(1)=1, a(3)=16 differ mod 2 (start n>=2 of the mod-2 clause is sharp)")

lines.append(f"TOTAL: {npass} pass, {nfail} fail")
print("\n".join(lines))
with open(OUT, "w") as fh: fh.write("\n".join(lines) + "\n")
