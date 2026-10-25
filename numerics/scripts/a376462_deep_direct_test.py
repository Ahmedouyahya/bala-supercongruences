#!/usr/bin/env python3
"""
Direct test of BOTH A376462 congruences at depths beyond all earlier runs
(earlier: p in {5,7,11,13}, m <= 3, r <= 2, and (5,3,1)).
  shifted: a(m p^r - 1) = a(m p^(r-1) - 1)  (mod p^(3r))
  first:   a(m p^r)     = a(m p^(r-1))      (mod p^(3r))
a(n) computed straight from the OEIS definition (no reuse of project code).
Output: numerics/out/a376462_deep_direct_test.txt
"""
import sys, time, os
from math import comb

def A108625_row(n):
    # A108625(n,k) = sum_{i<=k} C(n,i)^2 C(n+k-i, k-i), for k = 0..n
    return [sum(comb(n, i)**2 * comb(n + k - i, k - i) for i in range(k + 1)) for k in range(n + 1)]

def a(n):
    if n < 0:
        raise ValueError
    row = A108625_row(n)
    return sum(comb(n, k)**2 * comb(n + k, k) * row[n - k] for k in range(n + 1))

def vp(x, p):
    if x == 0:
        return 'inf'
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

# sanity: OEIS data
data = [1,5,109,3317,121501,4954505,216867925,9981053045,476860000285,23451310381505,1180189308268609,60519806861966105]
assert [a(n) for n in range(len(data))] == data, "definition mismatch with OEIS data"

cases = [(7,2,3),(7,2,4),(17,2,1),(19,2,1),(23,2,1),(7,3,1),(5,3,2),(5,3,3),(5,4,1),(29,2,1),(31,2,1),(7,3,2)]
lines = ["(p,r,m) | N=m p^r | v_p(a(N-1)-a(N/p-1)) vs 3r | v_p(a(N)-a(N/p)) vs 3r | seconds"]
print(lines[0]); sys.stdout.flush()
cache = {}
def A(n):
    if n not in cache:
        cache[n] = a(n)
    return cache[n]
for (p, r, m) in cases:
    t0 = time.time()
    N1, N0 = m * p**r, m * p**(r - 1)
    vs = vp(A(N1 - 1) - A(N0 - 1), p)
    vf = vp(A(N1) - A(N0), p)
    ok_s = (vs == 'inf') or vs >= 3 * r
    ok_f = (vf == 'inf') or vf >= 3 * r
    line = f"({p},{r},{m}) | {N1} | shifted v={vs} need {3*r} {'OK' if ok_s else 'FAIL'} | first v={vf} need {3*r} {'OK' if ok_f else 'FAIL'} | {time.time()-t0:.1f}"
    print(line); sys.stdout.flush()
    lines.append(line)
here = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(here, "out", "a376462_deep_direct_test.txt"), "w") as fh:
    fh.write("\n".join(lines) + "\n")
