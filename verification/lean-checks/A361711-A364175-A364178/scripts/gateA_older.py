"""Gate A for A361711, A364175, A364178 (2026-10-16): the Lean target definitions mirrored in Python and compared with the
OEIS b-files (directory given as argv[1]; downloaded files are only parsed as integers).
A361711: the target's match/sum definition in Z. A364175/A364178: (i) the exact integer formula Num/Den that the Lean proof
shows equal to the target's `a` (theorems a_eq_B175, a_eq_B178), for every b-file term; (ii) the target's Gamma-ratio
definition itself, round(...).toNat, evaluated with mpmath at a precision of (number of digits of the value + 40), for n <= 40."""
import sys, os, mpmath
from math import comb, factorial, prod
D = sys.argv[1]; mpmath.mp.dps = 80
def C(n, k): return comb(n, k) if 0 <= k <= n else 0
def a361711(n):
    if n == 0: return 0
    if n == 1: return 1
    m = n - 2
    return sum((-1) ** k * C(n, k) * C(n, k) * C(m, k) for k in range(m + 1))
def b175(n):
    num = 3 ** n * factorial(6 * n); den = factorial(3 * n) * factorial(2 * n) * prod(2 * n + 3 * j for j in range(1, n + 1))
    assert num % den == 0; return num // den
def b178(n):
    num = 2 ** n * factorial(10 * n) * factorial(3 * n); den = factorial(6 * n) * factorial(5 * n) * factorial(n) * prod(n + 2 * j for j in range(1, n + 1))
    assert num % den == 0; return num // den
def g175(n):
    mpmath.mp.dps = len(str(b175(n))) + 40
    r = mpmath.mpf(n); G = mpmath.gamma
    v = G(6 * r + 1) * G(mpmath.mpf(2) / 3 * r + 1) / (G(3 * r + 1) * G(2 * r + 1) * G(mpmath.mpf(5) / 3 * r + 1))
    return max(int(mpmath.nint(v)), 0)
def g178(n):
    mpmath.mp.dps = len(str(b178(n))) + 40
    r = mpmath.mpf(n); G = mpmath.gamma
    v = G(10 * r + 1) * G(3 * r + 1) * G(r / 2 + 1) / (G(6 * r + 1) * G(5 * r + 1) * G(3 * r / 2 + 1) * G(r + 1))
    return max(int(mpmath.nint(v)), 0)
fails = 0
def rows(f): return [tuple(map(int, l.split())) for l in open(os.path.join(D, f)) if l.strip() and not l.startswith("#")]
for name, f, fn, nmax in [("A361711", a361711, "b361711.txt", 400), ("A364175 (Num/Den)", b175, "b364175.txt", 400), ("A364178 (Num/Den)", b178, "b364178.txt", 400)]:
    rs = [r for r in rows(fn) if r[0] <= nmax]; bad = [n for n, v in rs if f(n) != v]; fails += len(bad)
    print(f"{name}: {len(rs)} b-file terms (n = {rs[0][0]}..{rs[-1][0]}), mismatches: {bad[:5] if bad else 0}")
for name, g, f in [("A364175 Gamma definition", g175, b175), ("A364178 Gamma definition", g178, b178)]:
    bad = [n for n in range(0, 41) if g(n) != f(n)]; fails += len(bad)
    print(f"{name} vs Num/Den, n = 0..40 (precision: digits of the value + 40): mismatches: {bad[:5] if bad else 0}")
print("FAILURES:", fails)
