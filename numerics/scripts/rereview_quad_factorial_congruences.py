# Re-review (fact-only) of notes/A364175-A364178-factorial-ratio-towers.md -- congruences at the stated moduli, with slack.
# Run: ~/venvs/general/bin/python -I numerics/rereview_quad_factorial_congruences.py > numerics/out/rereview_quad_factorial_congruences.txt
# G1  Lemma 2 (cited): S_1 == 0 mod p^{2e}, S_2 == 0 mod p^e, p in {5,7,11,13}, e<=3 (p=5: e<=4); and p=3 behaviour
# G2  Lemma A: U(aN) == W_r^{an} mod p^{3r}, p in {5,7,11,13}, r<=3, n<=4 and n=p, a in {1,2,3,5,6,10}; P_b == 1 mod p^{3r} each b; p=3 failure
# G3  Lemma B: prod_{p∤k<=N}(1+cN/(dk)) == 1 mod p^{3r}, c in {-3,-1,1,2,3,5}, d in {1,2,3,4,7} (p∤d); H^(1) == 0 mod p^{2r}; H^(2) == 0 mod p^r;
#       log-term bounds j=1: >= 3r, j=2: >= 3r, j>=3: jr - v_p(j) >= 3r
# G4  Theorem 3: v_p(a(N)/a(M)-1) >= 3r, v_p(b(N)/b(M)-1) >= 3r; difference form; p|n cases; slack recorded
# G5  Remark: balanced ratio F(pM)/F(M) == 1 mod p^{3r} for JK C(2N,N) and Bober (20,6,1;12,10,3,2)
# G6  Remark 4: v_p(a(np^r)) == v_p(a(n)); p=3 data for the b-tower; p=3 for the a-tower
from fractions import Fraction
from math import comb, factorial
from functools import reduce

def vp(x, p):
    x = Fraction(x)
    if x == 0:
        return 10**9
    a, b = x.numerator, x.denominator
    v = 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v

fails = 0; passes = 0
def check(cond, msg):
    global fails, passes
    if cond:
        passes += 1
    else:
        fails += 1
        print("FAIL:", msg)

def prod(it, start=1):
    return reduce(lambda x, y: x * y, it, start)
def U(X, p):
    return prod((k for k in range(1, X + 1) if k % p), 1)
def a_int(n):
    return Fraction(3 ** n * factorial(6 * n), factorial(3 * n) * factorial(2 * n) * prod(2 * n + 3 * j for j in range(1, n + 1)))
def b_int(n):
    return Fraction(2 ** n * factorial(10 * n) * factorial(3 * n), factorial(6 * n) * factorial(5 * n) * factorial(n) * prod(n + 2 * j for j in range(1, n + 1)))

print("== G1 Lemma 2 ==")
for p in (3, 5, 7, 11, 13):
    row = []
    for e in (1, 2, 3, 4):
        if p ** e > 3000:
            continue
        R = [u for u in range(1, p ** e) if u % p]
        S1 = sum(Fraction(1, u) for u in R); S2 = sum(Fraction(1, u * u) for u in R)
        row.append((e, vp(S1, p) - 2 * e, vp(S2, p) - e))
        if p >= 5:
            check(vp(S1, p) >= 2 * e and vp(S2, p) >= e, f"G1 p={p} e={e} v(S1)={vp(S1,p)} v(S2)={vp(S2,p)}")
    print(f"  p={p}: (e, slack S1 vs 2e, slack S2 vs e) = {row}")

print("== G2 Lemma A ==")
for p in (5, 7, 11, 13):
    worst = 10**9; worstP = 10**9
    for r in (1, 2, 3):
        for n in (1, 2, 3, 4, p):
            N = n * p ** r
            if 10 * N > 6000:
                continue
            W = U(p ** r, p)
            for a in (1, 2, 3, 5, 6, 10):
                d = vp(Fraction(U(a * N, p), W ** (a * n)) - 1, p) - 3 * r
                worst = min(worst, d)
                check(d >= 0, f"G2 p={p} r={r} n={n} a={a} slack {d}")
            # P_b individually
            Rr = [u for u in range(1, p ** r) if u % p]
            for b in range(0, 3 * n):
                Pb = prod((1 + Fraction(b * p ** r, u) for u in Rr), Fraction(1))
                dP = vp(Pb - 1, p) - 3 * r
                worstP = min(worstP, dP)
                check(dP >= 0, f"G2 P_b p={p} r={r} b={b} slack {dP}")
    print(f"  p={p}: Lemma A min slack {worst}; P_b min slack {worstP}")
# p = 3: does Lemma A hold?  record
row = []
for r in (1, 2, 3):
    for n in (1, 2):
        N = n * 3 ** r; W = U(3 ** r, 3)
        row.append((r, n, min(vp(Fraction(U(a * N, 3), W ** (a * n)) - 1, 3) - 3 * r for a in (1, 2, 3, 5, 6, 10))))
print("  p=3 Lemma A slack (r,n,slack):", row)

print("== G3 Lemma B ==")
for p in (5, 7, 11, 13):
    worst = 10**9
    for r in (1, 2, 3):
        for n in (1, 2, 3, p):
            N = n * p ** r
            if N > 1400:
                continue
            ks = [k for k in range(1, N + 1) if k % p]
            H1 = sum(Fraction(1, k) for k in ks); H2 = sum(Fraction(1, k * k) for k in ks)
            check(vp(H1, p) >= 2 * r, f"G3 H1 p={p} r={r} n={n} v={vp(H1,p)}")
            check(vp(H2, p) >= r, f"G3 H2 p={p} r={r} n={n} v={vp(H2,p)}")
            for c in (-3, -1, 1, 2, 3, 5):
                for d in (1, 2, 3, 4, 7):
                    if d % p == 0:
                        continue
                    P = prod((1 + Fraction(c * N, d * k) for k in ks), Fraction(1))
                    check(P != 0, f"G3 zero factor p={p} r={r} n={n} c={c} d={d}")
                    s = vp(P - 1, p) - 3 * r
                    worst = min(worst, s)
                    check(s >= 0, f"G3 p={p} r={r} n={n} c={c} d={d} slack {s}")
            # term bounds for j>=3
            for j in range(3, 60):
                check(j * r - vp(j, p) >= 3 * r, f"G3 j-term p={p} r={r} j={j}")
    print(f"  p={p}: Lemma B min slack {worst}")

print("== G4 Theorem 3 ==")
for p in (5, 7, 11, 13):
    for r in (1, 2, 3):
        for n in (1, 2, 3, 4, p):
            N = n * p ** r
            if 10 * N > 6000:
                continue
            M = N // p
            ra = vp(a_int(N) / a_int(M) - 1, p) - 3 * r; rb = vp(b_int(N) / b_int(M) - 1, p) - 3 * r
            da = vp(a_int(N) - a_int(M), p) - 3 * r; db = vp(b_int(N) - b_int(M), p) - 3 * r
            check(ra >= 0 and rb >= 0 and da >= 0 and db >= 0, f"G4 p={p} r={r} n={n} slacks ratio a/b {ra}/{rb} diff a/b {da}/{db}")
            check(a_int(N).denominator == 1 and a_int(M).denominator == 1 and b_int(N).denominator == 1 and b_int(M).denominator == 1, f"G4 integrality p={p} r={r} n={n}")
            print(f"  p={p} r={r} n={n}: ratio slack a={ra} b={rb}; difference slack a={da} b={db}; v_p(a(n))={vp(a_int(n),p)} v_p(b(n))={vp(b_int(n),p)}")

print("== G5 balanced ratios ==")
for p in (5, 7, 11):
    for r in (1, 2):
        for n in (1, 2):
            N = n * p ** r; M = N // p
            if 20 * N > 6000:
                continue
            jk = Fraction(comb(2 * N, N), comb(2 * M, M))
            bob = lambda m: Fraction(factorial(20 * m) * factorial(6 * m) * factorial(m), factorial(12 * m) * factorial(10 * m) * factorial(3 * m) * factorial(2 * m))
            s1 = vp(jk - 1, p) - 3 * r; s2 = vp(bob(N) / bob(M) - 1, p) - 3 * r
            check(s1 >= 0 and s2 >= 0, f"G5 p={p} r={r} n={n} slacks {s1} {s2}")
            print(f"  p={p} r={r} n={n}: C(2N,N) ratio slack {s1}; Bober(20,6,1;12,10,3,2) ratio slack {s2}")

print("== G6 remarks ==")
for p in (5, 7):
    for n in (1, 2, 3, p):
        vals = [vp(a_int(n * p ** r), p) for r in range(0, 3)]
        check(len(set(vals)) == 1, f"G6 v_p(a(np^r)) not constant p={p} n={n} {vals}")
print("  v_p(a(np^r)) constant in r (p in 5,7; n in 1,2,3,p; r<=2): ok")
for name, f in (("b", b_int), ("a", a_int)):
    row = []
    for r in (1, 2, 3):
        for n in (1, 2):
            N = n * 3 ** r
            if N > 400:
                continue
            row.append((n, r, vp(f(N) - f(N // 3), 3), 3 * r))
    print(f"  p=3 {name}-tower (n, r, v_3(diff), 3r):", row)
print(f"PASS {passes} FAIL {fails}")
