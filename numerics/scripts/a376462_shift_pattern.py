# Pattern probe: for which shifts c does a(m p^r + c) ≡ a(m p^{r-1} + c) (mod p^{3r}) hold for A376462?  Compare with Apéry numbers.
from math import comb
from functools import lru_cache
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
@lru_cache(None)
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
@lru_cache(None)
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
@lru_cache(None)
def apery(n): return sum(comb(n,k)**2*comb(n+k,k)**2 for k in range(n+1))
for name,f in (("A376462",a),("Apery",apery)):
    print(name)
    for p in (5,7,11):
        for r in (1,2):
            row=[]
            for c in range(-3,4):
                vals=[]
                for m in (1,2,3):
                    N=m*p**r+c; M=m*p**(r-1)+c
                    if M<0 or (r==2 and N>400): vals.append(None); continue
                    vals.append(vp(f(N)-f(M),p)-3*r)
                row.append((c,vals))
            print(f"  p={p} r={r}: " + "  ".join(f"c={c}:{v}" for c,v in row))
