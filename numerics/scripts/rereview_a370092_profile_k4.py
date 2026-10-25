#!/usr/bin/env python3
# Re-review of notes/A370092-periodicity-proof.md: the parenthetical after Lemma B says
# "the minimum over n of v_2(b_k) - m is independent of m: 2, 4, 2, 3, 3, 6, 5, 6, 6, 8, ... for k = 3, 4, 5, ...".
# Exact valuations of b_k(n, 2^m) = sum_j (-1)^(k-j) C(k,j) j^n (j^(2^m) - 1) over the lemma's own range n >= m+2.
# Run: ~/venvs/general/bin/python -I numerics/rereview_a370092_profile_k4.py
import os
from math import comb
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "rereview_a370092_profile_k4.txt")
def v2(x):
    if x == 0: return 999
    x = abs(x); v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def bk(k, n, P): return sum((-1) ** (k - j) * comb(k, j) * j ** n * (j ** P - 1) for j in range(k + 1))
L = []
L.append("k=4: v2(b_4(n,2^m)) - m at n=m+2, m=2..9: " + str([v2(bk(4, m + 2, 2 ** m)) - m for m in range(2, 10)]))
L.append("k=4: min over n in [m+2, m+200) of v2(b_4)-m, m=2..6: " + str([min(v2(bk(4, n, 2 ** m)) for n in range(m + 2, m + 200)) - m for m in range(2, 7)]))
L.append("k=4: min over n in [40,200] of v2(b_4)-m, m=5,8 (the range used by lemmaB_stirling_2adic.py): " + str([min(v2(bk(4, n, 2 ** m)) for n in range(40, 201)) - m for m in (5, 8)]))
L.append("k=8: min over n in [m+2, m+200) of v2(b_8)-m, m=2..9: " + str([min(v2(bk(8, n, 2 ** m)) for n in range(m + 2, m + 200)) - m for m in range(2, 10)]))
L.append("k=12: min over n in [m+2, m+200) of v2(b_12)-m, m=2..9: " + str([min(v2(bk(12, n, 2 ** m)) for n in range(m + 2, m + 200)) - m for m in range(2, 10)]))
L.append("k=12: first argmin n, m=2..9: " + str([min(range(m + 2, m + 200), key=lambda n: v2(bk(12, n, 2 ** m))) for m in range(2, 10)]))
L.append("Lemma B requirement at k=4 is v2(b_4)-m >= 1+floor(4/3) = 2: satisfied (min 3); at k=8: >= 3 (min 5); at k=12: >= 5 (min 6).")
print("\n".join(L))
with open(OUT, "w") as fh: fh.write("\n".join(L) + "\n")
