"""Gates A and B for the A386548 Lean proof. usage: python3 -I gateAB.py <dir containing b386548.txt>"""
import sys, os
from math import comb
def vp(x, p):
    if x == 0: return 10**9
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
def a_target(n):
    # def a (n : N) : Z := sum_{k in range (n/2+1)} sign * C(n+k-1, k) * C(n-k-1, n-2k), natural subtraction
    s = 0
    for k in range(n // 2 + 1):
        sign = 1 if k % 2 == 0 else -1
        t1 = comb(max(n + k - 1, 0), k)
        t2 = comb(max(n - k - 1, 0), max(n - 2 * k, 0))
        s += sign * t1 * t2
    return s
def a_series(N):
    # [x^N] (1-x^2)^N (1+x^3)^(-N) = sum_{2j+3k=N} (-1)^(j+k) C(N,j) C(N+k-1,k)
    if N == 0:
        return 1
    s = 0
    for k in range(N // 3 + 1):
        r = N - 3 * k
        if r % 2: continue
        j = r // 2
        s += (-1) ** (j + k) * comb(N, j) * comb(N + k - 1, k)
    return s
def a_direct(N):
    # [x^N] ((1-x)/(1-x+x^2))^N by exact power-series arithmetic
    L = N + 1
    inv = [0] * L; inv[0] = 1                      # 1/(1-x+x^2)
    for i in range(1, L):
        inv[i] = inv[i - 1] - (inv[i - 2] if i >= 2 else 0)
    g = [0] * L                                     # (1-x) * inv
    for i in range(L):
        g[i] = inv[i] - (inv[i - 1] if i >= 1 else 0)
    pw = [1] + [0] * (L - 1)
    for _ in range(N):
        pw = [sum(pw[i] * g[m - i] for i in range(m + 1)) for m in range(L)]
    return pw[N]
fails = 0
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 20: print("FAIL", m)
rows = [tuple(map(int, l.split())) for l in open(os.path.join(sys.argv[1], "b386548.txt")) if l.strip() and not l.startswith("#")]
for n, v in rows: check(a_target(n) == v, f"A target vs b-file n={n}")
print(f"Gate A: target definition vs OEIS b-file: {len(rows)} terms (n = {rows[0][0]}..{rows[-1][0]})")
for N in range(0, 61): check(a_target(N) == a_series(N) == a_direct(N), f"B1 identity N={N}")
for N in range(61, 301): check(a_target(N) == a_series(N), f"B1 identity N={N}")
print("Gate B1: target formula = sum over 2j+3k=N (N <= 300) = direct series coefficient (N <= 60)")
c = 0
for p in [5, 7, 11, 13]:
    for N in range(p, 6 * p * p, p):
        R = vp(N, p)
        for k in range(N // 3 + 1):
            r = N - 3 * k
            if r % 2: continue
            j = r // 2
            check((j % p == 0) == (k % p == 0), f"B2 sync p={p} N={N} j={j} k={k}")
            if j % p: check(vp(comb(N, j), p) >= R, f"B3 C(N,j) p={p} N={N} j={j}")
            if k % p: check(vp(comb(N + k - 1, k), p) >= R, f"B3 C(N+k-1,k) p={p} N={N} k={k}")
            if j % p and k % p:
                check(vp(comb(N, j) * comb(N + k - 1, k), p) >= 2 * R, f"B3 unscaled 2R p={p} N={N}")
            if j % p == 0 and k % p == 0:
                M, jj, kk = N // p, j // p, k // p
                TN = comb(N, j) * comb(N + k - 1, k); TM = comb(M, jj) * comb(M + kk - 1, kk)
                check(vp(TN - TM, p) >= 2 * R, f"B4 scaled 2R p={p} N={N} j'={jj}")
                check(vp(TN - TM, p) >= 3 * R, f"B4 scaled 3R p={p} N={N} j'={jj}")
                check((-1) ** (j + k) == (-1) ** (jj + kk), "B4 sign")
            c += 1
print(f"Gate B2-B4: synchronisation, unscaled valuations >= R and 2R, scaled terms congruent mod p^(2R) and p^(3R), signs: {c} index pairs")
c = 0; slack = []
for p in [5, 7, 11, 13]:
    for n in range(1, 7):
        for r in range(1, 4):
            if n * p ** r > 2500: continue
            v = vp(a_target(n * p ** r) - a_target(n * p ** (r - 1)), p)
            check(v >= 2 * r, f"B5 target congruence p={p} n={n} r={r} v={v}"); slack.append(v - 2 * r); c += 1
print(f"Gate B5: target congruence mod p^(2r): {c} cases, min slack {min(slack)}")
# JAC_bound as stated in Epoch's file: p^(v(C(m+j,j)) + 3 + v(m+j) + v(j) + v(m)) | C(p(m+j), pj) - C(m+j, j), 1 <= j <= m
c = 0
for p in [5, 7, 11]:
    for m in range(1, 40):
        for j in range(1, m + 1):
            e = vp(comb(m + j, j), p) + 3 + vp(m + j, p) + vp(j, p) + vp(m, p)
            check(vp(comb(p * (m + j), p * j) - comb(m + j, j), p) >= e, f"B6 JAC_bound p={p} m={m} j={j}"); c += 1
print(f"Gate B6: Epoch's JAC_bound statement: {c} cases")
print("FAILURES:", fails)
