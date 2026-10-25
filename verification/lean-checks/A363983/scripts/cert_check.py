"""Exact check of the Maxima Zeilberger certificate for A363983 (Gate B for the non-negativity step)."""
from fractions import Fraction as Fr
from math import comb, factorial
def C(n, k): return comb(n, k) if 0 <= k <= n else 0
def F(n, k):   # (-1)^(n+k) C(n,k) C(n+k-1,k) C(2k,n), with C(n+k-1,k) = 1 at n = k = 0
    if k < 0 or k > n: return 0
    return (-1) ** (n + k) * C(n, k) * (C(n + k - 1, k) if n + k >= 1 else 1) * C(2 * k, n)
def P(n, k):
    return (50*k*n**5 - 35*n**5 - 10*k**2*n**4 + 275*k*n**4 - 209*n**4 - 48*k**2*n**3 + 589*k*n**3 - 470*n**3
            - 74*k**2*n**2 + 596*k*n**2 - 488*n**2 - 40*k**2*n + 272*k*n - 228*n - 8*k**2 + 48*k - 40)
def G(n, k):   # R(n,k) F(n,k) with the pole (n-k+1)(n-k+2) cancelled against C(n,k): C(n,k)/((n-k+1)(n-k+2)) = n!/(k!(n-k+2)!)
    if k < 0 or k > n + 2: return Fr(0)
    base = Fr(factorial(n), factorial(k) * factorial(n - k + 2))
    return Fr(-k * (n - 2 * k) * (n - 2 * k + 1) * P(n, k), n * (n + 1)) * (-1) ** (n + k) * base * (C(n + k - 1, k) if n + k >= 1 else 1) * C(2 * k, n)
c0 = lambda n: 3*n*(3*n+1)*(3*n+2)*(5*n**2+14*n+10)
c1 = lambda n: -((n+1)*(145*n**4+551*n**3+694*n**2+324*n+56))
c2 = lambda n: 2*(n+1)*(n+2)**2*(5*n**2+4*n+1)
def a(n): return sum(F(n, k) for k in range(n + 1))
bad = 0; cnt = 0
for n in range(1, 41):
    for k in range(0, n + 4):
        lhs = c0(n) * F(n, k) + c1(n) * F(n + 1, k) + c2(n) * F(n + 2, k)
        rhs = G(n, k + 1) - G(n, k)
        cnt += 1
        if Fr(lhs) != rhs: bad += 1
print(f"certificate identity c0 F(n,k) + c1 F(n+1,k) + c2 F(n+2,k) = G(n,k+1) - G(n,k): {cnt} (n,k), failures {bad}")
bad2 = sum(1 for n in range(1, 200) if c0(n) * a(n) + c1(n) * a(n + 1) + c2(n) * a(n + 2) != 0)
print("recurrence c0 a(n) + c1 a(n+1) + c2 a(n+2) = 0 for 1 <= n < 200: failures", bad2)
print("boundary: G(n,0) = 0 and G(n, n+3) = 0 for n <= 40:", all(G(n, 0) == 0 and G(n, n + 3) == 0 for n in range(1, 41)))
