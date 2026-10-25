#!/usr/bin/env python3
"""
Self-contained finite verification for the exceptional k in Lemma B of notes/A370092-periodicity-proof.md.
S_1(k; n, m) := sum_{t=0}^{floor((k-1)/2)} (-1)^{k-1-2t} C(k, 2t+1) (1+2t)^n t (1 + (2^m - 1) t)   (an integer).
Claim: v_2(S_1) >= d := floor(k/3) for k in {3, 6, 7, 15} (d = 1, 2, 2, 5), all m >= 2, all n >= m + 2.
Reduction to finitely many cases: mod 2^d, S_1 depends on n only through (1+2t)^n mod 2^d, which is periodic in n
with period dividing lambda(2^d) (1, 2, 2, 8), and on m only through (2^m - 1) mod 2^d, which is constant for m >= d.
So it suffices to test m = 2..d (plus one m >= d) and, for each m, 2*8 consecutive n starting at n = m + 2.
We test more than that: m = 2..9 and 32 consecutive n from m + 2.  Output: numerics/out/lemmaB_k15_residue_check.txt
"""
from math import comb
import os
def v2(x):
    if x == 0: return 99
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def S1(k, n, m):
    return sum((-1)**(k-1-2*t) * comb(k, 2*t+1) * (1+2*t)**n * t * (1 + (2**m - 1)*t) for t in range((k-1)//2 + 1))
lines = []
bad = 0
for k, d in ((3,1), (6,2), (7,2), (15,5)):
    worst = 99; cases = 0
    for m in range(2, 10):
        for n in range(m+2, m+2+32):
            v = v2(S1(k, n, m)); cases += 1
            worst = min(worst, v)
            if v < d: bad += 1; lines.append(f"VIOLATION k={k} m={m} n={n} v2(S1)={v} < {d}")
    lines.append(f"k={k}: need v2(S1) >= {d}; tested m=2..9, n=m+2..m+33 ({cases} cases); min v2(S1) = {worst}")
lines.append(f"violations: {bad}")
print("\n".join(lines))
here = os.path.dirname(os.path.abspath(__file__))
open(os.path.join(here, "out", "lemmaB_k15_residue_check.txt"), "w").write("\n".join(lines) + "\n")
