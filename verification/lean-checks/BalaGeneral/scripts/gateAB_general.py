"""Gate A/B for BalaGeneral: mirror of the Lean definitions aRS, aRSn (truncated power series over Z,
binomialSeries = generalized binomial coefficients, rescale(-1) = x -> -x), compared with OEIS data,
and the conjectured congruences tested numerically."""
import json, sys, os
from math import factorial
D = sys.argv[1]
def gchoose(t, k):  # Ring.choose t k for integer t
    num = 1
    for i in range(k): num *= (t - i)
    return num // factorial(k)
def bS(t, L): return [gchoose(t, k) for k in range(L + 1)]
def rescale_neg(f): return [c * (-1) ** k for k, c in enumerate(f)]
def mul(f, g, L): return [sum(f[i] * g[k - i] for i in range(k + 1)) for k in range(L + 1)]
def pw(f, n, L):
    r = [1] + [0] * L
    for _ in range(n): r = mul(r, f, L)
    return r
def aRS(r, s, n): L = n; return pw(mul(bS(r, L), rescale_neg(bS(s, L)), L), n, L)[n]
def aRSn(r, s, n): L = r * n; return pw(mul(bS(s, L), rescale_neg(bS(-s, L)), L), n, L)[r * n]
def oeis(a):
    j = json.load(open(os.path.join(D, f"A{a}.json"))); rec = j[0] if isinstance(j, list) else j["results"][0]
    return rec["offset"], [int(x) for x in rec["data"].split(",")], rec["revision"]
cases = [("000984",2,0),("001700",0,-1),("002003",1,-1),("091527",3,-1),("119259",2,-1),("156894",1,-2),
         ("165817",0,-2),("234839",1,2),("348410",-1,-2),("351857",-2,-4),("352373",-1,-3)]
bad = 0
for a, r, s in cases:
    off, data, rev = oeis(a)
    off = int(str(off).split(",")[0])
    vals = {n: aRS(r, s, n) for n in range(1, 16)}
    # align: Bala's a(r,s;n), n >= 1, with the OEIS terms; A001700 "with offset 1" means a(r,s;n) = A001700(n-1)
    shift = 1 if a == "001700" else 0
    mism = [n for n in range(1, 16) if 0 <= n - shift - off < len(data) and vals[n] != data[n - shift - off]]
    cmp_n = [n for n in range(1, 16) if 0 <= n - shift - off < len(data)]
    bad += len(mism)
    print(f"A{a} (r,s)=({r},{s}) rev {rev}: compared n={cmp_n[0]}..{cmp_n[-1]}, mismatches {mism}")
for a, r, s in [("333715",3,1),("002003",1,1),("103885",2,1)]:
    off, data, rev = oeis(a); off = int(str(off).split(",")[0])
    cmp_n = [n for n in range(1, 13) if 0 <= n - off < len(data)]
    mism = [n for n in cmp_n if aRSn(r, s, n) != data[n - off]]
    bad += len(mism)
    print(f"A{a} a(r,s,n) (r,s)=({r},{s}) rev {rev}: compared n={cmp_n[0]}..{cmp_n[-1]}, mismatches {mism}")
print("Gate A mismatches:", bad)
def v(x, p):
    if x == 0: return 10**9
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
fails = 0; tests = 0; minslack = 10**9
for p in (5, 7, 11):
    for r in range(-4, 5):
        for s in range(-4, 5):
            for n in (1, 2, 3):
                for k in ((1, 2) if p == 5 else (1,)):
                    d = aRS(r, s, n * p ** k) - aRS(r, s, n * p ** (k - 1)); tests += 1
                    sl = v(d, p) - 3 * k; minslack = min(minslack, sl)
                    if sl < 0: fails += 1; print("FAIL aRS", p, r, s, n, k)
for p in (5, 7):
    for r in range(1, 4):
        for s in range(-3, 4):
            for n in (1, 2):
                d = aRSn(r, s, n * p) - aRSn(r, s, n); tests += 1
                sl = v(d, p) - 3; minslack = min(minslack, sl)
                if sl < 0: fails += 1; print("FAIL aRSn", p, r, s, n)
print(f"Gate B: {tests} congruence tests, {fails} failures, minimal slack {minslack}")
