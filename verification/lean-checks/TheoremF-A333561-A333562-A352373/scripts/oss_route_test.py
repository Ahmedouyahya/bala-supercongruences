"""Does the term-by-term (Osburn-Sahu-Straub style) route work for the Theorem F instances?
A(N) = sum_k t(N,k); split k into scaled (p | k) and unscaled (p does not divide k).
Test: (i) each scaled term t(N, pk') == t(M, k') mod p^(3r); (ii) the unscaled sum == 0 mod p^(3r); (iii) each unscaled term == 0 mod p^(2r)."""
from math import comb
def C(n, k): return comb(n, k) if 0 <= k <= n else 0
def vp(x, p):
    if x == 0: return 10**9
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
# term functions t(N, k) for the target formulas
def t333561(N, k): return C(3 * N, 2 * N - k) * C(N + k - 1, k)          # k in 0..2N
def t333562(N, k): return C(4 * N, 3 * N - k) * C(N + k - 1, k)          # coefficient form [x^{3N}](1+x)^{4N}(1-x)^{-N}
def t352373(N, k): return C(3 * N - 2 * k - 1, N - 2 * k) * C(N + k - 1, k)  # k in 0..N/2 (target formula)
cases = [("A333561 [x^2N](1+x)^3N(1-x)^-N", t333561, lambda N: range(0, 2 * N + 1)),
         ("A333562 [x^3N](1+x)^4N(1-x)^-N", t333562, lambda N: range(0, 3 * N + 1)),
         ("A352373 target formula", t352373, lambda N: range(0, N // 2 + 1))]
for name, t, rng in cases:
    worst_scaled = 10**9; worst_unscaled_sum = 10**9; worst_unscaled_term = 10**9; total_ok = True
    for p in [5, 7, 11]:
        for m in [1, 2, 3]:
            for r in [1, 2]:
                N = m * p ** r; M = N // p
                if N > 400: continue
                S_N = sum(t(N, k) for k in rng(N) if k % p == 0)
                for k in rng(N):
                    if k % p == 0:
                        worst_scaled = min(worst_scaled, vp(t(N, k) - t(M, k // p), p) - 3 * r)
                    else:
                        worst_unscaled_term = min(worst_unscaled_term, vp(t(N, k), p) - 2 * r)
                U = sum(t(N, k) for k in rng(N) if k % p)
                worst_unscaled_sum = min(worst_unscaled_sum, vp(U, p) - 3 * r)
                tot = sum(t(N, k) for k in rng(N)) - sum(t(M, k) for k in rng(M))
                total_ok &= vp(tot, p) >= 3 * r
    print(f"{name}: theorem holds {total_ok}; min slack scaled-termwise(3r) {worst_scaled}; unscaled terms(2r) {worst_unscaled_term}; unscaled sum(3r) {worst_unscaled_sum}")
