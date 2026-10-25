#!/usr/bin/env python3
"""
Direct deep test of Theorem F (p >= 5) and Theorem F_3 (p = 3) for A(N) = [x^{cN}] ((1+x)^a (1-x)^b)^N,
at depths beyond the earlier sweeps (which had r <= 3, c <= 3, -4 <= a,b <= 5).
Here: a, b in [-5, 7], c in 1..4, (r, m) with N = m p^r, r up to 4 (p = 3), r up to 3 (p = 5), r <= 2 (p = 7),
plus a small r = 5 sample at p = 3.  Claims tested:
  p >= 5 : v_p(A(N) - A(N/p)) >= 3r for all (a,b,c)
  p = 3  : v_3(A(N) - A(N/3)) >= 3r - 1 always; >= 3r if 3|c or a+b = c (mod 3) or a = b = 0 (mod 3)
Everything from the definition, by incremental generalized binomials; no project code reused.
Output: numerics/out/theoremF_deep_direct_sweep.txt
"""
import os, sys, time

def genbinom_row(x, L):
    """[C(x,i) for i in 0..L] for integer x (any sign), via C(x,i+1) = C(x,i)(x-i)/(i+1) (exact)."""
    row = [1]
    c = 1
    for i in range(L):
        c = c * (x - i) // (i + 1)
        row.append(c)
    return row

def coeff(a, b, c, N):
    """[x^{cN}] (1+x)^{aN} (1-x)^{bN}."""
    L = c * N
    ra = genbinom_row(a * N, L)
    rb = genbinom_row(b * N, L)
    s = 0
    for i in range(L + 1):
        t = ra[i] * rb[L - i]
        s += t if (L - i) % 2 == 0 else -t
    return s

def vp(x, p):
    if x == 0:
        return 10**9
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

lines = []
def out(s):
    print(s); sys.stdout.flush(); lines.append(s)

plan = {3: [(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],
        5: [(1,1),(1,2),(2,1),(2,2),(3,1)],
        7: [(1,1),(1,2),(2,1)]}
A_RANGE = range(-5, 8); C_RANGE = range(1, 5)
fails = []
t0 = time.time()
for p, rms in plan.items():
    worst = {}
    for (r, m) in rms:
        N = m * p**r
        for a in A_RANGE:
            for b in A_RANGE:
                for c in C_RANGE:
                    A1 = coeff(a, b, c, N); A0 = coeff(a, b, c, N // p)
                    v = vp(A1 - A0, p)
                    if p >= 5:
                        need = 3 * r; cls = 'all'
                    else:
                        good = (c % 3 == 0) or ((a + b - c) % 3 == 0) or (a % 3 == 0 and b % 3 == 0)
                        need = 3 * r if good else 3 * r - 1; cls = 'good' if good else 'other'
                    slack = v - need
                    key = (p, cls)
                    worst[key] = min(worst.get(key, 10**9), slack)
                    if slack < 0:
                        fails.append((p, r, m, a, b, c, v, need))
        out(f"p={p} (r,m)=({r},{m}) N={N} done; worst slack so far {worst}; {time.time()-t0:.0f}s")
# r = 5 sample at p = 3
for (r, m) in [(5,1),(5,2)]:
    N = m * 3**r
    for a in range(-2, 5):
        for b in range(-2, 5):
            for c in range(1, 4):
                A1 = coeff(a, b, c, N); A0 = coeff(a, b, c, N // 3)
                v = vp(A1 - A0, 3)
                good = (c % 3 == 0) or ((a + b - c) % 3 == 0) or (a % 3 == 0 and b % 3 == 0)
                need = 3 * r if good else 3 * r - 1
                if v - need < 0:
                    fails.append((3, r, m, a, b, c, v, need))
    out(f"p=3 (r,m)=({r},{m}) N={N} done; {time.time()-t0:.0f}s")
out(f"FAILURES: {len(fails)}")
for f in fails[:50]:
    out(f"  FAIL (p,r,m,a,b,c,v,need) = {f}")
here = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(here, "out", "theoremF_deep_direct_sweep.txt"), "w") as fh:
    fh.write("\n".join(lines) + "\n")
