# Re-review (fact-only) of notes/A386548-quadratic-tower-proof.md -- exact identities.
# Run: ~/venvs/general/bin/python -I numerics/rereview_quad_A386548_identities.py > numerics/out/rereview_quad_A386548_identities.txt
# Tests (all exact, Fraction/comb):
#  I1  formula (1) [sum over 2j+3k=N of (-1)^{j+k} C(N,j) C(N+k-1,k)] == direct series coefficient [x^N]((1-x)/(1-x+x^2))^N
#  I2  formula (1) == OEIS formula sum_k (-1)^k C(n+k-1,k) C(n-k-1,n-2k)  (n>=1)
#  I3  first terms a(0..7) == 1, 0, -2, -3, 6, 25, 1, -147
#  I4  (T1) identity C(N,j) = (N/j) C(N-1,j-1); (T2) identity C(N+k-1,k) = (N/k) C(N+k-1,k-1); and the ratio formula in (T2)
#  I5  general forms v_p(C(N,j)) >= v_p(N)-v_p(j), v_p(C(N+k-1,k)) >= v_p(N)-v_p(k) (p in {2,3,5,7})
#  I6  C(pD-1,pk') = (M/D) C(pD,pk'),  C(D-1,k') = (M/D) C(D,k')  with D = M+k'
#  I7  identity (2): T_N/T_M = Q1*Q2 for every scaled pair, including boundary pairs j'=0 / k'=0 (Q=1)
#  I8  synchronisation: p | N, 2j+3k=N  =>  (p|j <=> p|k), for p>=5; and failure at p=3 exhibited
#  I9  sign matching (-1)^{p(j'+k')} = (-1)^{j'+k'} for odd p
#  I10 valuation bookkeeping of case s<r-1: v(j')=v(k')=s, v(M-j')=s, v(D)=s, v(D-k')=r-1; and v_p(T_M) >= 2(r-1-s)
from fractions import Fraction
from math import comb

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

def a_formula1(N):
    tot = 0
    for k in range(0, N // 3 + 1):
        rem = N - 3 * k
        if rem % 2:
            continue
        j = rem // 2
        tot += (-1) ** (j + k) * comb(N, j) * (1 if k == 0 else comb(N + k - 1, k))  # C(-1,0)=1 convention at N=0
    return tot

def a_oeis(n):
    if n == 0:
        return 1
    return sum((-1) ** k * comb(n + k - 1, k) * comb(n - k - 1, n - 2 * k) for k in range(n // 2 + 1))

def series_mul(A, B, L):
    C = [0] * (L + 1)
    for i, x in enumerate(A):
        if x == 0:
            continue
        for j, y in enumerate(B):
            if i + j > L:
                break
            C[i + j] += x * y
    return C

def series_pow(A, e, L):
    R = [1] + [0] * L
    for _ in range(e):
        R = series_mul(R, A, L)
    return R

def a_direct(N):
    # (1-x)/(1-x+x^2) = (1-x) * sum of periodic (1,1,0,-1,-1,0)
    L = N
    pat = [1, 1, 0, -1, -1, 0]
    inv = [pat[i % 6] for i in range(L + 1)]
    f = [inv[i] - (inv[i - 1] if i >= 1 else 0) for i in range(L + 1)]
    return series_pow(f, N, L)[N] if N > 0 else 1

fails = 0; passes = 0
def check(cond, msg):
    global fails, passes
    if cond:
        passes += 1
    else:
        fails += 1
        print("FAIL:", msg)

# I1, I2, I3
for N in range(0, 61):
    f1 = a_formula1(N)
    check(f1 == a_direct(N), f"I1 N={N}: formula(1)={f1} direct={a_direct(N)}")
    check(f1 == a_oeis(N), f"I2 N={N}: formula(1)={f1} oeis={a_oeis(N)}")
first = [a_formula1(N) for N in range(8)]
check(first == [1, 0, -2, -3, 6, 25, 1, -147], f"I3 first terms {first}")
print("I1/I2: formula (1) == direct series == OEIS formula for N<=60; I3 first terms:", first)

# I4
for N in range(1, 80):
    for j in range(1, N + 1):
        check(Fraction(comb(N, j)) == Fraction(N, j) * comb(N - 1, j - 1), f"I4 T1 N={N} j={j}")
    for k in range(1, 80):
        check(Fraction(comb(N + k - 1, k)) == Fraction(N, k) * comb(N + k - 1, k - 1), f"I4 T2 N={N} k={k}")
        from math import factorial
        check(Fraction(factorial(k - 1) * factorial(N), factorial(k) * factorial(N - 1)) == Fraction(N, k), f"I4 T2-ratio N={N} k={k}")
print("I4: (T1),(T2) identities exact for N<80, j<=N, k<80")

# I5
worst = {}
for p in (2, 3, 5, 7):
    w = 10**9
    for N in range(1, 200):
        for j in range(1, N + 1):
            d = vp(comb(N, j), p) - (vp(N, p) - vp(j, p)); w = min(w, d)
            check(d >= 0, f"I5 C(N,j) p={p} N={N} j={j}")
        for k in range(1, 120):
            d = vp(comb(N + k - 1, k), p) - (vp(N, p) - vp(k, p)); w = min(w, d)
            check(d >= 0, f"I5 C(N+k-1,k) p={p} N={N} k={k}")
    worst[p] = w
print("I5: general forms hold for N<200; min slack per p:", worst)

# I6, I7, I8, I9, I10
def scaled_pairs(M):
    out = []
    for kp in range(0, M // 3 + 1):
        rem = M - 3 * kp
        if rem % 2:
            continue
        out.append((rem // 2, kp))
    return out

for p in (5, 7, 11, 13):
    for r in (1, 2, 3):
        for n in (1, 2, 3, 4, 5, 6, p):
            N = n * p ** r
            if N > 1600:
                continue
            M = N // p
            R = vp(N, p)  # = r unless p | n
            # I8 synchronisation
            for k in range(0, N // 3 + 1):
                rem = N - 3 * k
                if rem % 2:
                    continue
                j = rem // 2
                check((j % p == 0) == (k % p == 0), f"I8 sync p={p} N={N} j={j} k={k}")
            seen_boundary = 0
            for (jp, kp) in scaled_pairs(M):
                j, k = p * jp, p * kp
                D = M + kp
                # I6
                check(Fraction(comb(p * D - 1, p * kp)) == Fraction(M, D) * comb(p * D, p * kp), f"I6a p={p} N={N} j'={jp} k'={kp}")
                check(Fraction(comb(D - 1, kp)) == Fraction(M, D) * comb(D, kp), f"I6b p={p} N={N} j'={jp} k'={kp}")
                TN = comb(p * M, p * jp) * comb(p * M + p * kp - 1, p * kp)
                TM = comb(M, jp) * comb(M + kp - 1, kp)
                check(TM != 0, f"I7 T_M=0 at p={p} N={N} j'={jp} k'={kp}")
                Q1 = Fraction(comb(p * M, p * jp), comb(M, jp))
                Q2 = Fraction(comb(p * D, p * kp), comb(D, kp))
                check(Fraction(TN, TM) == Q1 * Q2, f"I7 identity (2) p={p} N={N} j'={jp} k'={kp}")
                if jp == 0 or kp == 0:
                    seen_boundary += 1
                    check((jp != 0 or Q1 == 1) and (kp != 0 or Q2 == 1), f"I7 boundary Q!=1 p={p} N={N} j'={jp} k'={kp}")
                # I9
                check((-1) ** (j + k) == (-1) ** (jp + kp), f"I9 sign p={p} N={N}")
                # I10 bookkeeping, using R = v_p(N) as the note prescribes
                s = min(vp(jp, p), vp(kp, p))
                if s < R - 1:
                    check(vp(jp, p) == s and vp(kp, p) == s, f"I10 v(j')=v(k')=s fails p={p} N={N} j'={jp} k'={kp}")
                    check(vp(M - jp, p) == s, f"I10 v(M-j') p={p} N={N} j'={jp}")
                    check(vp(D, p) == s, f"I10 v(D) p={p} N={N} k'={kp}")
                    check(vp(D - kp, p) == R - 1, f"I10 v(D-k') p={p} N={N} k'={kp}")
                    check(vp(TM, p) >= 2 * (R - 1 - s), f"I10 v(T_M)>=2(R-1-s) p={p} N={N} j'={jp} k'={kp} v={vp(TM,p)} need={2*(R-1-s)}")
                else:
                    check(jp % p ** (R - 1) == 0 and kp % p ** (R - 1) == 0 and M % p ** (R - 1) == 0, f"I10 case2 divisibility p={p} N={N}")
                    if jp == 0 or kp == 0:
                        check(s == vp(M, p), f"I10 boundary s=v(M) p={p} N={N} j'={jp} k'={kp}")
print("I6-I10: identities, synchronisation, signs, case bookkeeping checked for p in {5,7,11,13}, r<=3, n in {1..6,p}, N<=1600")

# I8 failure at p = 3 (the note says 3 | uv = 6 breaks synchronisation): exhibit a counterexample
bad3 = [(j, k) for N in (3, 6, 9) for k in range(N // 3 + 1) for j in [(N - 3 * k) // 2] if (N - 3 * k) % 2 == 0 and ((j % 3 == 0) != (k % 3 == 0))]
print("I8 at p=3: pairs with p|j xor p|k (N in 3,6,9):", bad3[:6])
check(len(bad3) > 0, "I8 expected synchronisation failure at p=3 not observed")

print(f"PASS {passes} FAIL {fails}")
