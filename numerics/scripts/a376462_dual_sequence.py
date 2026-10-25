# Dual sequence b(n) = sum_{k,j} (-1)^{k+j} C(n+k,k)^2 C(n,k) C(n+k+j,k+j)^2 C(n,j).
# Claim (Straub-style negative-index extension): a(N-1) = b(-N) and b(N-1) = a(-N) for the common 6-parameter family.
# Tests: (1) verify a(N-1) = F(-N) with the Gamma-limit binomials; (2) does b satisfy b(mp^r) ≡ b(mp^{r-1}) (mod p^{3r})?  (3) b(mp^r-1) ≡ b(mp^{r-1}-1)?
from math import comb
from functools import lru_cache
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def gbin(n,k):
    # Straub (8): lim_{z->0} Gamma(z+n+1)/(Gamma(z+k+1)Gamma(z+n-k+1)) for integers n,k
    if k>=0 and n-k>=0: return comb(n,k)
    if n<0 and k>=0:  # (-1)^k C(k-n-1,k)
        return (-1)**k*comb(k-n-1,k)
    if n<0 and n-k>=0:  # k<0, n-k>=0: (-1)^{n-k} C(-k-1,-n-1)
        return (-1)**(n-k)*comb(-k-1,-n-1)
    return 0
def F(n1,n2,n3,n4,n5,n6,K=200):
    # sum over k,j in a finite window where terms can be nonzero
    tot=0
    for k in range(-K,K+1):
        t1=gbin(n1,k)*gbin(n2,k)*gbin(n3+k,k)
        if t1==0: continue
        for j in range(-K,K+1):
            t2=gbin(n4,k+j)*gbin(n5,k+j)*gbin(n6+j,j)
            if t2: tot+=t1*t2
    return tot
@lru_cache(None)
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
@lru_cache(None)
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
@lru_cache(None)
def b(n): return sum((-1)**(k+j)*comb(n+k,k)**2*comb(n,k)*comb(n+k+j,k+j)**2*comb(n,j) for k in range(n+1) for j in range(n+1))
print("F(n,..,n)=a(n) for n=0..6:", all(F(*(n,)*6,K=40)==a(n) for n in range(7)))
print("F(-N,..,-N)=b(N-1) for N=1..6:", all(F(*(-N,)*6,K=40)==b(N-1) for N in range(1,7)))
print("b(n), n=0..8:", [b(n) for n in range(9)])
for p in (5,7,11,13):
    for r in (1,2):
        res0=[];res1=[]
        for m in (1,2,3):
            N=m*p**r; M=m*p**(r-1)
            if N>350: continue
            res0.append(vp(b(N)-b(M),p)-3*r)
            res1.append(vp(b(N-1)-b(M-1),p)-3*r)
        print(f"p={p} r={r}: slack b(mp^r)-b(mp^(r-1)) = {res0};  slack b(mp^r-1)-b(mp^(r-1)-1) = {res1}")
