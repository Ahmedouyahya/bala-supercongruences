"""A333565 bridge, exact integers. S(n,K) = sum_{j<=K} C(n+j-1,j) 2^j; B(n) = S(n,n) = sum_k C(2n,n-k) C(n+k-1,k).
(i)  S(n,K) = S(n-1,K) + 2 S(n,K-1)                     (n >= 2, K >= 1; Pascal)
(ii) B(n) + B(n-1) = 2^n C(2n,n) - 2^n C(2n-2,n-2)       (n >= 1; from (i))
(iii) e_n := d_n + 4 d_{n-1} (target, before toNat) = 2B(n) - (-1)^n, and e_n >= 1."""
from math import comb
def C(n,k): return comb(n,k) if 0<=k<=n else 0
S=lambda n,K: sum(C(n+j-1,j)*2**j for j in range(K+1))
B=lambda n: sum(C(2*n,n-k)*C(n+k-1,k) for k in range(n+1)) if n>0 else 1
b=lambda m: 2**m*C(2*m,m)
d=lambda i: sum((-1)**k*b(i-k) for k in range(i+1))
e=lambda n: d(n)+4*(d(n-1) if n>0 else 0)
f=0
f+=sum(1 for n in range(2,40) for K in range(1,60) if S(n,K)!=S(n-1,K)+2*S(n,K-1))
f+=sum(1 for n in range(1,80) if S(n,n)!=B(n))
f+=sum(1 for n in range(1,80) if B(n)+B(n-1)!=2**n*C(2*n,n)-2**n*C(2*n-2,n-2))
f+=sum(1 for n in range(0,80) if e(n)!=2*B(n)-(-1)**n or e(n)<1)
print("failures:",f)
