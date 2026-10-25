#!/usr/bin/env python3
# Independent re-review of notes/A370092-periodicity-proof.md, part 5: powers of two up to 2^12 with many periods of data.
# a(n) mod 2^13 computed from identity (1): a(n) = sum_k c_k S(n,k), with c_k = k! g_k reduced mod 2^13 and the
# Stirling rows S(n,.) mod 2^13 (exact modular arithmetic; cross-checked against the exact recurrence for n<=400).
# Checks for alpha = 1..12: Prop. 2 (period 2^(alpha-1), start alpha+1 for alpha>=3; 2 from 3 for alpha=2; 2 from 2 for
# alpha=1), the true preperiod, and that 2^(alpha-2) is NOT an eventual period (alpha>=3).
# Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_pow2_deep.py [N]   (default N=7000, ~2-3 min)
import os, sys
from fractions import Fraction as Fr
from math import comb

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_pow2_deep.txt")
N = int(sys.argv[1]) if len(sys.argv) > 1 else 7000
AMAX = 12
MOD = 2 ** (AMAX + 1)
lines = []
npass = nfail = 0
def rec(ok, msg):
    global npass, nfail
    if ok: npass += 1
    else: nfail += 1
    lines.append(("PASS " if ok else "FAIL ") + msg)
def info(msg): lines.append("INFO " + msg)

# c_k mod MOD
g0, g1, g2 = Fr(1), Fr(1), Fr(1)
cmod = [1, 1, 2]
gs = [g0, g1, g2]
fact = 2
for k in range(3, N + 1):
    gk = gs[k - 2] + gs[k - 3] / 2
    gs.append(gk)
    fact *= k
    ck = gk * fact
    assert ck.denominator == 1
    cmod.append(int(ck) % MOD)
    if k >= 3: gs[k - 3] = None  # free memory (keep only the last 3 g's needed)
# Stirling rows mod MOD and a(n) mod MOD
amod = [1]
row = [1]            # S(0,0)
for n in range(1, N + 1):
    new = [0] * (n + 1)
    for k in range(1, n + 1):
        new[k] = (k * row[k] + row[k - 1]) % MOD if k < n else row[k - 1] % MOD
    row = new
    amod.append(sum(cmod[k] * row[k] for k in range(1, n + 1)) % MOD)
# cross-check with the exact recurrence for n<=400
w = [1 + 2 ** j - 3 ** j for j in range(401)]
a = [1]
for n in range(1, 401):
    s = 0; C = 1
    for j in range(1, n + 1):
        C = C * (n - j + 1) // j
        s += C * w[j] * a[n - j]
    a.append(1 - s // 2)
rec(all(a[n] % MOD == amod[n] for n in range(401)), f"modular Stirling computation of a(n) mod 2^{AMAX+1} agrees with exact recurrence for n<=400")

def start_for_period(r, P):
    L = len(r); st = L - P
    while st > 0 and r[st - 1 + P] == r[st - 1]: st -= 1
    return st
rows = []; okP2 = oklam = True
for e in range(1, AMAX + 1):
    q = 2 ** e; P = 2 if e <= 2 else 2 ** (e - 1)
    r = [x % q for x in amod]
    st = start_for_period(r, P)
    claimed = 2 if e == 1 else (3 if e == 2 else e + 1)
    periods_of_data = (N - st) / P
    if st > claimed: okP2 = False
    lam = 1 if e == 1 else (2 if e == 2 else 2 ** (e - 2))
    st_lam = start_for_period(r, lam)
    last_fail = max([n for n in range(0, N - lam) if r[n + lam] != r[n]] or [-1])
    lam_period = st_lam <= N // 2
    if e >= 3 and lam_period: oklam = False
    rows.append((q, P, st, claimed, round(periods_of_data, 1), lam, lam_period, last_fail))
rec(okP2, f"Prop. 2 for alpha=1..{AMAX}: period 2^(alpha-1) (2 for alpha<=2) from the claimed start, N={N}")
rec(oklam, f"alpha=3..{AMAX}: lambda(2^alpha) = 2^(alpha-2) is not an eventual period (failures up to n close to N)")
info("(2^alpha, P, true preperiod, claimed start, #periods of data after preperiod, lambda, lambda-is-period, last n where lambda-shift fails): ")
for row_ in rows: info("   " + str(row_))
info("alpha where true preperiod == claimed start alpha+1: " + str([e for e, row_ in zip(range(1, AMAX + 1), rows) if row_[2] == row_[3]]))
info("alpha where true preperiod < claimed start: " + str([(e, row_[2]) for e, row_ in zip(range(1, AMAX + 1), rows) if row_[2] < row_[3]]))
lines.append(f"TOTAL: {npass} pass, {nfail} fail")
print("\n".join(lines))
with open(OUT, "w") as fh: fh.write("\n".join(lines) + "\n")
