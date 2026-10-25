# Independent re-review (2026-10-15): A363983 theorem a(mp^r) == a(mp^{r-1}) mod p^{3r} at larger primes / depths than any
# existing output file (sweep stops at N <= 400; a363983_oss_steps at N <= 600).  Exact integers.
# Run: ~/venvs/general/bin/python -I numerics/rereview_oss_a363983_wider.py > numerics/out/rereview_oss_a363983_wider.txt
from math import comb
def vp(x, p):
    if x == 0: return 10**9
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
def a(n):
    if n == 0: return 1
    return sum((-1) ** (n + k) * comb(n, k) * comb(n + k - 1, k) * comb(2 * k, n) for k in range((n + 1) // 2, n + 1))
cases = [(13, 1, m) for m in range(1, 7)] + [(13, 2, 1), (13, 2, 2), (13, 2, 3), (13, 3, 1), (17, 1, 1), (17, 1, 2), (17, 2, 1), (19, 2, 1), (23, 2, 1), (29, 1, 3), (31, 2, 1)] + [(13, 1, 13), (13, 2, 13)]
bad = 0
for p, r, m in cases:
    N = m * p ** r
    v = vp(a(N) - a(N // p), p)
    ok = v >= 3 * r
    bad += (not ok)
    print(f"{'PASS' if ok else 'FAIL'} p={p} r={r} m={m} N={N}: v_p(a(N)-a(N/p)) = {v}, need {3*r}, slack {v-3*r}")
print(f"SUMMARY rereview_oss_a363983_wider: PASS {len(cases)-bad}, FAIL {bad}")
