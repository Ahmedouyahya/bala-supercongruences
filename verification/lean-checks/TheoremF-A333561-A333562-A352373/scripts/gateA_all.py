"""Gate A for the remaining targets: mirror each Lean definition (natural subtraction, toNat, Q) and compare with OEIS b-files."""
import sys, os
from math import comb
from fractions import Fraction
D = sys.argv[1]
def nsub(a, b): return a - b if a >= b else 0
def C(n, k): return comb(n, k) if 0 <= k <= n else 0
def a333561(n):  # sum_{k<2n+1} C(3n, 2n-k) * C(n+k-1, k)   (natural subtraction)
    return sum(C(3 * n, nsub(2 * n, k)) * C(nsub(n + k, 1), k) for k in range(2 * n + 1))
def a333562(n):  # sum_{j<3n+1} C(n+j-1, j) * 2^j
    return sum(C(nsub(n + j, 1), j) * 2 ** j for j in range(3 * n + 1))
def a352373(n):  # if n = 0 then 0 else sum_{k <= n/2} C(3n-2k-1, n-2k) * C(n+k-1, k)
    if n == 0: return 0
    return sum(C(nsub(3 * n - 2 * k, 1), nsub(n, 2 * k)) * C(nsub(n + k, 1), k) for k in range(n // 2 + 1))
def a333565(n):  # b_m = 2^m C(2m,m); d_n = sum (-1)^k b_{n-k}; a = (d_n + 4 d_{n-1}).toNat
    b = lambda m: 2 ** m * C(2 * m, m)
    d = lambda t: sum((-1) ** k * b(t - k) for k in range(t + 1))
    v = d(n) + (4 * d(n - 1) if n != 0 else 0)
    return v if v > 0 else 0
def a370092_all(N):  # a(0)=1; a(m+1) = (-1)^(m+1) + 1/2 sum_{j=1}^{m+1} C(m+1,j)(1-(-1)^j-(-2)^j) a(m+1-j); value: numerator
    a = [Fraction(1)]
    for m1 in range(1, N + 1):
        s = sum(C(m1, j) * (1 - (-1) ** j - (-2) ** j) * a[m1 - j] for j in range(1, m1 + 1))
        a.append(Fraction((-1) ** m1) + Fraction(1, 2) * s)
    return a
def a108625(n, k):  # sum_{i<=k} C(n,i)^2 C(n+k-i, k-i)
    return sum(C(n, i) ** 2 * C(n + k - i, k - i) for i in range(k + 1))
def a376462(n):
    return sum(C(n, k) ** 2 * C(n + k, k) * a108625(n, nsub(n, k)) for k in range(n + 1))
fails = 0
def cmp(name, f, fname, nmax=None):
    global fails
    rows = [tuple(map(int, l.split())) for l in open(os.path.join(D, fname)) if l.strip() and not l.startswith("#")]
    if nmax: rows = [r for r in rows if r[0] <= nmax]
    bad = [n for n, v in rows if f(n) != v]
    fails += len(bad)
    print(f"{name}: {len(rows)} b-file terms (n = {rows[0][0]}..{rows[-1][0]}), mismatches: {bad[:5] if bad else 0}")
cmp("A333561", a333561, "b333561.txt", 300)
cmp("A333562", a333562, "b333562.txt", 300)
cmp("A352373", a352373, "b352373.txt", 300)
cmp("A333565", a333565, "b333565.txt", 300)
A = a370092_all(400)
print("A370092: all terms integers for n <= 400:", all(x.denominator == 1 for x in A))
cmp("A370092", lambda n: A[n].numerator, "b370092.txt", 400)
cmp("A376462", a376462, "b376462.txt", 150)
print("FAILURES:", fails)
