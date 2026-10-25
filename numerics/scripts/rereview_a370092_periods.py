#!/usr/bin/env python3
# Independent re-review of notes/A370092-periodicity-proof.md, part 4: the period statements and their start indices.
# Exact a(n) for n<=N; for each modulus: does a(n+P) == a(n) (mod q) hold for every n >= claimed start?  What is the
# true preperiod n0 (smallest start) for that P, and the minimal eventual period?
# Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_periods.py [N]
import os, sys
from math import comb, gcd
from fractions import Fraction as Fr

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_periods.txt")
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
lines = []
npass = nfail = 0
def rec(ok, msg):
    global npass, nfail
    if ok: npass += 1
    else: nfail += 1
    lines.append(("PASS " if ok else "FAIL ") + msg)
def info(msg): lines.append("INFO " + msg)

# exact a(n) via the e.g.f. recurrence 2a(n) = 2 - sum_{j>=1} C(n,j)(1+2^j-3^j) a(n-j)
w = [1 + 2 ** j - 3 ** j for j in range(N + 1)]
a = [1]
for n in range(1, N + 1):
    s = 0; C = 1
    for j in range(1, n + 1):
        C = C * (n - j + 1) // j
        s += C * w[j] * a[n - j]
    assert s % 2 == 0
    a.append(1 - s // 2)
rec(a[:7] == [1, 1, 3, 16, 105, 856, 8433], f"a(0..6) = {a[:7]}")

def factorize(k):
    f = {}; d = 2
    while d * d <= k:
        while k % d == 0: f[d] = f.get(d, 0) + 1; k //= d
        d += 1
    if k > 1: f[k] = f.get(k, 0) + 1
    return f
def phi(k):
    r = k
    for p in factorize(k): r = r // p * (p - 1)
    return r
def carmichael(k):
    f = factorize(k); L = 1
    for p, e in f.items():
        if p == 2: lp = 1 if e == 1 else (2 if e == 2 else 2 ** (e - 2))
        else: lp = (p - 1) * p ** (e - 1)
        L = L * lp // gcd(L, lp)
    return L
def start_for_period(r, P):
    """smallest n0 such that r[n+P]==r[n] for all n0<=n<=len(r)-1-P ; len(r)-P if never"""
    L = len(r); st = L - P
    while st > 0 and r[st - 1 + P] == r[st - 1]: st -= 1
    return st
def min_period(r, Pmax):
    """smallest P<=Pmax whose start is <= len(r)//2 (eventual period supported by at least half the data)"""
    for P in range(1, Pmax + 1):
        st = start_for_period(r, P)
        if st <= len(r) // 2: return P, st
    return None, None

# ---- (i) the Theorem for all 3<=k<=KMAX
KMAX = 400
bad = []; slack_hist = {}; table = []
for k in range(3, KMAX + 1):
    r = [x % k for x in a]; f = factorize(k)
    claimed = max(f.values()) + 1
    P = phi(k)
    st = start_for_period(r, P)
    Pmin, stmin = min_period(r, P)
    ok = st <= claimed and st <= N - P - 200   # the congruence verified from 'claimed' over a long tail
    if not ok: bad.append((k, P, st, claimed))
    slack_hist[claimed - st] = slack_hist.get(claimed - st, 0) + 1
    table.append((k, P, st, claimed, Pmin, stmin))
rec(not bad, f"Theorem: a(n+phi(k)) == a(n) (mod k) for all n >= max_(p^alpha||k) alpha+1, 3<=k<={KMAX}, N={N}; violations {bad[:10]}")
info("histogram of (claimed start - true preperiod for period phi(k)) over 3<=k<=400: " + str(dict(sorted(slack_hist.items()))))
rec(all(P % Pmin == 0 for (k, P, st, cl, Pmin, stmin) in table), "minimal eventual period divides phi(k) for all 3<=k<=400")
info("k<=400 where the true preperiod equals the claimed start: " + str([k for (k, P, st, cl, Pmin, stmin) in table if st == cl]))
info("k<=400 with minimal period == phi(k): " + str([k for (k, P, st, cl, Pmin, stmin) in table if Pmin == P]))
info("k<=60 table (k, phi, preperiod for phi, claimed start, min period, its start): " + str(table[:58]))
# is the Theorem's start ever violated when 'max alpha + 1' is replaced by 'max alpha' ?  (information only)
tight = [(k, st) for (k, P, st, cl, Pmin, stmin) in table if st == cl]
info("cases where start = max alpha + 1 is needed (true preperiod equals claimed start): " + str(tight[:30]))

# ---- (ii) odd prime powers: Prop. 1 (start alpha), minimal period
rows = []; okP1 = True; okmin = True
for p, emax in ((3, 6), (5, 4), (7, 3), (11, 2), (13, 2)):
    for e in range(1, emax + 1):
        q = p ** e; P = (p - 1) * p ** (e - 1)
        if 3 * P + 20 > N: continue
        r = [x % q for x in a]
        st = start_for_period(r, P)
        Pmin, stmin = min_period(r, P)
        rows.append((q, P, st, e, Pmin))
        if st > e: okP1 = False
        if Pmin != P: okmin = False
rec(okP1, "Prop. 1: a(n+phi(p^alpha)) == a(n) (mod p^alpha) for all n >= alpha (odd prime powers tested)")
rec(okmin, "odd prime powers tested: minimal eventual period == phi(p^alpha) = lambda(p^alpha)")
info("odd prime powers (q, phi, true preperiod, alpha, minimal period): " + str(rows))
info("odd prime powers where the true preperiod equals alpha (Prop. 1 start sharp): " + str([q for (q, P, st, e, Pmin) in rows if st == e]))

# ---- (iii) powers of two: Prop. 2 and sharpness vs lambda
rows = []; okP2 = True; oklam = True; okmin2 = True
for e in range(1, 11):
    q = 2 ** e; P = 2 if e <= 2 else 2 ** (e - 1)
    if 3 * P + 20 > N: continue
    r = [x % q for x in a]
    st = start_for_period(r, P)
    claimed = e + 1
    if st > claimed: okP2 = False
    lam = carmichael(q)
    st_lam = start_for_period(r, lam)
    lam_is_period = st_lam <= N // 2
    if e >= 3 and lam_is_period: oklam = False
    Pmin, stmin = min_period(r, P)
    if Pmin != P: okmin2 = False
    # last n at which the lambda-shift fails
    last_fail = max([n for n in range(0, N - lam) if r[n + lam] != r[n]] or [-1])
    rows.append((q, P, st, claimed, lam, lam_is_period, last_fail, Pmin))
rec(okP2, "Prop. 2: a(n+2^(alpha-1)) == a(n) (mod 2^alpha) for n >= alpha+1 (alpha>=3); mod 4 period 2 from 3; mod 2 period 2 from 2")
rec(oklam, "alpha>=3: lambda(2^alpha)=2^(alpha-2) is NOT an eventual period mod 2^alpha (fails at arbitrarily large n in range)")
rec(okmin2, "minimal eventual period mod 2^alpha equals 2^(alpha-1) (alpha>=2), 2 (alpha=1)")
info("powers of two (q, P, true preperiod, claimed start, lambda, lambda-is-period, last n where lambda-shift fails, min period): " + str(rows))
# the mod-2 and mod-4 start indices exactly
r2 = [x % 2 for x in a]; r4 = [x % 4 for x in a]
rec(start_for_period(r2, 2) == 2, f"mod 2: true preperiod for period 2 is {start_for_period(r2, 2)} (Prop. 2 says 2)")
rec(start_for_period(r4, 2) == 3, f"mod 4: true preperiod for period 2 is {start_for_period(r4, 2)} (Prop. 2 says 3)")
rec(start_for_period(r2, 1) > N // 2, "mod 2: period 1 is not an eventual period (so k=2 has period 2 != phi(2))")

# ---- (iv) the lcm/assembly step on examples with mixed prime factors: check start max(alpha_i, alpha+1) too
bad = []
for k in (6, 10, 12, 14, 18, 20, 24, 36, 40, 48, 56, 72, 80, 96, 100, 112, 120, 144, 160, 192, 200, 240, 288, 320, 360, 384, 400):
    f = factorize(k); r = [x % k for x in a]; P = phi(k)
    st = start_for_period(r, P)
    alt = max([e for p, e in f.items() if p != 2] + [f.get(2, 0) + 1 if 2 in f else 0])
    if st > alt: bad.append((k, st, alt))
rec(not bad, f"assembly: start max(alpha_i [odd], alpha_2+1) also suffices on sample composite k; violations {bad}")

lines.append(f"TOTAL: {npass} pass, {nfail} fail")
print("\n".join(lines))
with open(OUT, "w") as fh: fh.write("\n".join(lines) + "\n")
