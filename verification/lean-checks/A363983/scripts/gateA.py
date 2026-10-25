"""Gate A for A363983 plus the non-negativity route. usage: python3 -I gateA.py <dir with b363983.txt>"""
import sys, os
from math import comb
from fractions import Fraction
def s(n):   # the target's integer sum before toNat: sum_{k<=n} (-1)^(n+k) C(n,k) C(n+k-1,k) C(2k,n), with (n+k).pred
    return sum((-1) ** (n + k) * comb(n, k) * comb(max(n + k - 1, 0), k) * comb(2 * k, n) for k in range(n + 1))
def a_target(n):
    v = s(n); return v if v > 0 else 0          # Int.toNat
fails = 0
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 10: print("FAIL", m)
rows = [tuple(map(int, l.split())) for l in open(os.path.join(sys.argv[1], "b363983.txt")) if l.strip() and not l.startswith("#")]
for n, v in rows: check(a_target(n) == v, f"b-file n={n}")
print(f"Gate A: target (with toNat) vs b-file: {len(rows)} terms (n = {rows[0][0]}..{rows[-1][0]})")
vals = [s(n) for n in range(0, 801)]
check(all(v > 0 for v in vals), "positivity")
print("positivity of the integer sum, n <= 800:", all(v > 0 for v in vals))
# OEIS P-recurrence: 2 n^2 (n-1) (5n^2-16n+13) a(n) = (n-1)(145n^4-609n^3+868n^2-480n+96) a(n-1) - 3 (n-2)(3n-4)(3n-5)(5n^2-6n+2) a(n-2)
for n in range(2, 801):
    L = 2 * n * n * (n - 1) * (5 * n * n - 16 * n + 13) * vals[n]
    R = (n - 1) * (145 * n**4 - 609 * n**3 + 868 * n**2 - 480 * n + 96) * vals[n - 1] - 3 * (n - 2) * (3 * n - 4) * (3 * n - 5) * (5 * n * n - 6 * n + 2) * vals[n - 2]
    check(L == R, f"recurrence n={n}")
print("P-recurrence holds for 2 <= n <= 800")
rat = [Fraction(vals[n], vals[n - 1]) for n in range(1, 801)]
print("ratios a(n)/a(n-1) for n=1..8:", [round(float(r), 3) for r in rat[:8]], " min over n>=2:", round(float(min(rat[1:])), 4), " at n =", 2 + rat[1:].index(min(rat[1:])))
# induction route: if a(n-1) >= c*a(n-2) > 0 then a(n) >= c*a(n-1) ? test c = 7 symbolically per n: need coefficient condition
c = Fraction(7)
ok = True
for n in range(3, 801):
    A = 2 * n * n * (n - 1) * (5 * n * n - 16 * n + 13)
    B = (n - 1) * (145 * n**4 - 609 * n**3 + 868 * n**2 - 480 * n + 96)
    C = 3 * (n - 2) * (3 * n - 4) * (3 * n - 5) * (5 * n * n - 6 * n + 2)
    # a(n) = (B a(n-1) - C a(n-2))/A >= (B - C/c) a(n-1)/A ; need (B - C/c)/A >= c
    if not (B - C / c >= c * A): ok = False; print("induction step fails at n =", n); break
print("induction a(n) >= 7 a(n-1) from the recurrence works for all 3 <= n <= 800:", ok)
print("FAILURES:", fails)
