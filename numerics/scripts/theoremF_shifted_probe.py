# Do the univariate Theorem F sequences A(n) = [x^{cn}] phi^n have SHIFTED towers A(mp^r - 1) ≡ A(mp^{r-1} - 1) (mod p^{3r})?  (sandbox for A376462's shifted problem)
from math import comb
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def gb(e,i):
    num=1
    for t in range(i): num*=(e-t)
    den=1
    for t in range(1,i+1): den*=t
    return num//den
def A(a,b,c,N):
    if N<0: return None
    K=c*N
    Ac=[gb(a*N,i) for i in range(K+1)]; B=[gb(b*N,i)*(-1)**i for i in range(K+1)]
    return sum(Ac[i]*B[K-i] for i in range(K+1))
for (a,b,c) in ((2,-1,1),(3,-1,2),(4,-1,3),(-1,-3,1),(1,-1,1),(1,-1,2),(2,0,1),(1,1,1),(2,-2,1)):
    out=[]
    for p in (5,7,11):
        for r in (1,2):
            for m in (1,2):
                N=m*p**r; M=m*p**(r-1)
                if c*N>500: continue
                for sh in (-1,1):
                    x=A(a,b,c,N+sh); y=A(a,b,c,M+sh)
                    if x is None or y is None: continue
                    out.append(f"p{p}r{r}m{m}s{sh:+d}:{vp(x-y,p)-3*r:+d}")
    print(f"({a},{b},{c}): "+" ".join(out))
