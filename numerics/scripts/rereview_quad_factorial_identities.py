# Re-review (fact-only) of notes/A364175-A364178-factorial-ratio-towers.md -- exact identities and the integrality argument.
# Run: ~/venvs/general/bin/python -I numerics/rereview_quad_factorial_identities.py > numerics/out/rereview_quad_factorial_identities.txt
# F1  integer forms == Gamma-definition forms (exact rationals), first terms as printed in the note
# F2  Gamma(1+2n/3)/Gamma(1+5n/3) = 3^n/prod(2n+3j), Gamma(1+n/2)/Gamma(1+3n/2) = 2^n/prod(n+2j)  (as exact products)
# F3  v_2 formulas: v_2(2^n(10n)!(3n)!/((6n)!(5n)!n!)) = 2n+s_2(n); even n=2m: prod(n+2j) = 2^n (3m)!/m!, v_2(b)=s_2(3m); odd n: v_2(b)=2n+s_2(n)
# F4  odd q: N_k = floor(n/q^k) + eps_k, eps_k in {0,1}; eps_k = 1 iff exists s in [1,rho] with q^k | rho+2s; eps_k=1 => rho/q^k >= 1/3
# F5  Legendre reduction: v_q(b(n)) == sum_k [F(rho_k/q^k) - eps_k] exactly (q in {3,5,7,11,13}, n<=300)
# F6  F table on [0,1): values on the stated intervals; F>=1 on [3/10,1)
# F7  Radcliffe's F = floor(6x)-floor(3x)-floor(2x): values 0/1/2, zero only on [0,1/6); eps=1 => rho/q^k >= 1/5 (q != 3)
# F8  a(3m) = (18m)!(2m)!/((9m)!(6m)!(5m)!); b(2m) = (20m)!(6m)!m!/((12m)!(10m)!(3m)!(2m)!)
# F9  Lemma C: X! = p^{floor(X/p)} floor(X/p)! U(X)
# F10 Theorem 3 ratio identities, exact, p in {5,7,11,13}, r<=3, n<=4 and n=p (p|n), 10N <= 6000
# F11 Remark 3 shape: v^N prod(a_i N)!^{eps_i} / prod_{j<=N}(uN+vj) ratio identity (generic check with (u,v)=(1,3), factorials (4;2,1))
from fractions import Fraction
from math import comb, factorial, floor
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

def a_int(n):  # A364175 integer form
    return Fraction(3 ** n * factorial(6 * n), factorial(3 * n) * factorial(2 * n) * prod(2 * n + 3 * j for j in range(1, n + 1)))
def b_int(n):  # A364178 integer form
    return Fraction(2 ** n * factorial(10 * n) * factorial(3 * n), factorial(6 * n) * factorial(5 * n) * factorial(n) * prod(n + 2 * j for j in range(1, n + 1)))
def a_gamma(n):  # (6n)!/((3n)!(2n)!) * Gamma(1+2n/3)/Gamma(1+5n/3), with Gamma ratio = 1/prod_{j=1}^n (2n/3+j)
    return Fraction(factorial(6 * n), factorial(3 * n) * factorial(2 * n)) / prod((Fraction(2 * n, 3) + j for j in range(1, n + 1)), Fraction(1))
def b_gamma(n):
    return Fraction(factorial(10 * n) * factorial(3 * n), factorial(6 * n) * factorial(5 * n) * factorial(n)) / prod((Fraction(n, 2) + j for j in range(1, n + 1)), Fraction(1))

print("== F1/F2 ==")
for n in range(0, 61):
    check(a_int(n) == a_gamma(n), f"F1 a n={n}")
    check(b_int(n) == b_gamma(n), f"F1 b n={n}")
    check(prod((Fraction(2 * n, 3) + j for j in range(1, n + 1)), Fraction(1)) == Fraction(prod(2 * n + 3 * j for j in range(1, n + 1)), 3 ** n), f"F2 a n={n}")
    check(prod((Fraction(n, 2) + j for j in range(1, n + 1)), Fraction(1)) == Fraction(prod(n + 2 * j for j in range(1, n + 1)), 2 ** n), f"F2 b n={n}")
print("  a(0..5):", [a_int(n) for n in range(6)], " b(0..4):", [b_int(n) for n in range(5)])
check([a_int(n) for n in range(5)] == [1, 36, 3564, 408408, 49697388], "F1 a first terms")
check([b_int(n) for n in range(5)] == [1, 168, 83980, 48664320, 29966636700], "F1 b first terms")

print("== F3 v_2 ==")
s2 = lambda x: bin(x).count("1")
for n in range(1, 121):
    core = Fraction(2 ** n * factorial(10 * n) * factorial(3 * n), factorial(6 * n) * factorial(5 * n) * factorial(n))
    check(vp(core, 2) == 2 * n + s2(n), f"F3 core n={n}")
    check(s2(10 * n) == s2(5 * n) and s2(6 * n) == s2(3 * n), f"F3 digit sums n={n}")
    if n % 2 == 0:
        m = n // 2
        check(prod(n + 2 * j for j in range(1, n + 1)) == 2 ** n * factorial(3 * m) // factorial(m), f"F3 even product n={n}")
        check(vp(prod(n + 2 * j for j in range(1, n + 1)), 2) == 2 * n - s2(3 * m) + s2(m), f"F3 even v2 product n={n}")
        check(vp(b_int(n), 2) == s2(3 * m), f"F3 v2(b) even n={n}")
    else:
        check(all((n + 2 * j) % 2 == 1 for j in range(1, n + 1)), f"F3 odd factors n={n}")
        check(vp(b_int(n), 2) == 2 * n + s2(n), f"F3 v2(b) odd n={n}")
print("  v_2 formulas verified for n<=120")

print("== F4/F5/F6 odd q ==")
def F(x):
    return floor(10 * x) + floor(3 * x) - floor(6 * x) - floor(5 * x) - floor(x)
worst_summand = 10**9
for q in (3, 5, 7, 11, 13):
    for n in range(1, 301):
        total = 0; k = 1
        while True:
            qk = q ** k
            Nk = sum(1 for j in range(1, n + 1) if (n + 2 * j) % qk == 0)
            t, rho = divmod(n, qk)
            eps = Nk - t
            check(eps in (0, 1), f"F4 eps not in {{0,1}} q={q} k={k} n={n} eps={eps}")
            eps2 = int(any((rho + 2 * s) % qk == 0 for s in range(1, rho + 1)))
            check(eps == eps2, f"F4 eps characterisation q={q} k={k} n={n}")
            if eps == 1:
                check(3 * rho >= qk, f"F4 eps=1 but rho/q^k < 1/3: q={q} k={k} n={n} rho={rho}")
                check(all((rho + 2 * s) in (qk, 2 * qk) for s in range(1, rho + 1) if (rho + 2 * s) % qk == 0), f"F4 rho+2s not in {{q^k,2q^k}} q={q} k={k} n={n}")
            summand = F(Fraction(rho, qk)) - eps
            worst_summand = min(worst_summand, summand)
            # per-k Legendre summand equality
            leg = (10 * n) // qk + (3 * n) // qk - (6 * n) // qk - (5 * n) // qk - n // qk - Nk
            check(leg == summand, f"F5 per-k summand q={q} k={k} n={n}: legendre {leg} vs F-eps {summand}")
            total += summand
            if qk > 10 * n:
                break
            k += 1
        check(total == vp(b_int(n), q) if n <= 120 else True, f"F5 total q={q} n={n}")
print("  F4/F5 verified for q in {3,5,7,11,13}, n<=300 (exact b(n) comparison for n<=120); min summand F-eps =", worst_summand)
bps = sorted(set([Fraction(i, 10) for i in range(10)] + [Fraction(i, 6) for i in range(6)] + [Fraction(i, 5) for i in range(5)] + [Fraction(i, 3) for i in range(3)]))
table = [(str(b), F(b)) for b in bps]
print("  F6 F at breakpoints:", table)
expected = {Fraction(0): 0, Fraction(1, 10): 1, Fraction(1, 6): 0, Fraction(1, 5): 0, Fraction(3, 10): 1, Fraction(1, 3): 1, Fraction(2, 5): 1, Fraction(1, 2): 1,
            Fraction(3, 5): 1, Fraction(2, 3): 1, Fraction(7, 10): 2, Fraction(4, 5): 2, Fraction(5, 6): 1, Fraction(9, 10): 2}
check(all(F(b) == expected[b] for b in bps), "F6 table mismatch")
# fine grid check of the interval description
for i in range(0, 6000):
    x = Fraction(i, 6000)
    if x < Fraction(1, 10) or (Fraction(1, 6) <= x < Fraction(3, 10)):
        check(F(x) == 0, f"F6 zero region x={x}")
    elif (Fraction(1, 10) <= x < Fraction(1, 6)) or (Fraction(3, 10) <= x < Fraction(7, 10)) or (Fraction(5, 6) <= x < Fraction(9, 10)):
        check(F(x) == 1, f"F6 one region x={x} F={F(x)}")
    else:
        check(F(x) == 2, f"F6 two region x={x} F={F(x)}")

print("== F7 Radcliffe's F and A364175 eps ==")
G = lambda x: floor(6 * x) - floor(3 * x) - floor(2 * x)
for i in range(0, 6000):
    x = Fraction(i, 6000)
    val = G(x)
    check(val in (0, 1, 2), f"F7 G value x={x}")
    check((val == 0) == (x < Fraction(1, 6)), f"F7 zero set x={x}")
for q in (5, 7, 11, 13, 2):
    for n in range(1, 201):
        k = 1
        while q ** k <= 5 * n:
            qk = q ** k; t, rho = divmod(n, qk)
            Nk = sum(1 for j in range(1, n + 1) if (2 * n + 3 * j) % qk == 0)
            eps = Nk - t
            check(eps in (0, 1), f"F7 eps q={q} n={n} k={k}")
            if eps == 1:
                check(5 * rho >= qk, f"F7 eps=1 but rho/q^k<1/5 q={q} n={n} k={k}")
            check((6 * n) // qk - (3 * n) // qk - (2 * n) // qk - Nk == G(Fraction(rho, qk)) - eps, f"F7 legendre summand q={q} n={n} k={k}")
            k += 1
print("  verified (q in {2,5,7,11,13}, n<=200)")

print("== F8 reductions ==")
for m in range(1, 31):
    check(a_int(3 * m) == Fraction(factorial(18 * m) * factorial(2 * m), factorial(9 * m) * factorial(6 * m) * factorial(5 * m)), f"F8 a(3m) m={m}")
    check(b_int(2 * m) == Fraction(factorial(20 * m) * factorial(6 * m) * factorial(m), factorial(12 * m) * factorial(10 * m) * factorial(3 * m) * factorial(2 * m)), f"F8 b(2m) m={m}")
    # A364175, 3 ∤ n: 3^n (6n)!/((3n)!(2n)!) / prod(2n+3j) with no factor divisible by 3 -> v_3 >= n
for n in range(1, 61):
    if n % 3:
        check(all((2 * n + 3 * j) % 3 != 0 for j in range(1, n + 1)) and vp(a_int(n), 3) >= n, f"F8 v3 a(n)>=n n={n}")
print("  a(3m) Vasyunin form and b(2m) Bober form verified for m<=30")

print("== F9 Lemma C, F10 Theorem 3 identities ==")
def U(X, p):
    return prod((k for k in range(1, X + 1) if k % p), 1)
for p in (2, 3, 5, 7):
    for X in range(0, 200):
        check(factorial(X) == p ** (X // p) * factorial(X // p) * U(X, p), f"F9 p={p} X={X}")
cases = 0
for p in (5, 7, 11, 13):
    for r in (1, 2, 3):
        for n in (1, 2, 3, 4, p):
            N = n * p ** r
            if 10 * N > 6000:
                continue
            M = N // p
            L23 = prod((1 + Fraction(2 * N, 3 * k) for k in range(1, N + 1) if k % p), Fraction(1))
            L12 = prod((1 + Fraction(N, 2 * k) for k in range(1, N + 1) if k % p), Fraction(1))
            ida = a_int(N) / a_int(M) == Fraction(U(6 * N, p), U(3 * N, p) * U(2 * N, p) * U(N, p)) / L23
            idb = b_int(N) / b_int(M) == Fraction(U(10 * N, p) * U(3 * N, p), U(6 * N, p) * U(5 * N, p) * U(N, p) ** 2) / L12
            check(ida, f"F10 a identity p={p} r={r} n={n}")
            check(idb, f"F10 b identity p={p} r={r} n={n}")
            # intermediate steps of the derivation for b
            step1 = Fraction(factorial(10 * N) * factorial(3 * N), factorial(6 * N) * factorial(5 * N) * factorial(N)) == p ** M * Fraction(factorial(10 * M) * factorial(3 * M), factorial(6 * M) * factorial(5 * M) * factorial(M)) * Fraction(U(10 * N, p) * U(3 * N, p), U(6 * N, p) * U(5 * N, p) * U(N, p))
            step2 = prod(N + 2 * j for j in range(1, N + 1)) == p ** M * prod(M + 2 * jp for jp in range(1, M + 1)) * 2 ** (N - M) * U(N, p) * L12
            step3 = prod(2 * N + 3 * j for j in range(1, N + 1)) == p ** M * prod(2 * M + 3 * jp for jp in range(1, M + 1)) * 3 ** (N - M) * U(N, p) * L23
            check(step1 and step2 and step3, f"F10 derivation steps p={p} r={r} n={n}: {step1} {step2} {step3}")
            cases += 1
print(f"  Theorem 3 identities exact in {cases} cases (p in 5,7,11,13; r<=3; n in 1..4 and n=p; 10N<=6000)")

print("== F11 Remark 3 shape (generic) ==")
# ratio v^N (4N)! / ((2N)! N! prod_{j<=N}(uN+vj)) with sum eps_i a_i = 4-2-1 = 1, (u,v) = (1,3), p ∤ 3
def gen(n, u=1, v=3):
    return Fraction(v ** n * factorial(4 * n), factorial(2 * n) * factorial(n) * prod(u * n + v * j for j in range(1, n + 1)))
for p in (5, 7):
    for r in (1, 2):
        for n in (1, 2):
            N = n * p ** r; M = N // p
            lin = prod((1 + Fraction(N, 3 * k) for k in range(1, N + 1) if k % p), Fraction(1))
            check(gen(N) / gen(M) == Fraction(U(4 * N, p), U(2 * N, p) * U(N, p) * U(N, p)) / lin, f"F11 p={p} r={r} n={n}")
print("  generic shape identity holds (p in 5,7; r<=2; n<=2)")
print(f"PASS {passes} FAIL {fails}")
