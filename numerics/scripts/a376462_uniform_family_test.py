# Is there a Straub-type UNIFORM statement?  6-parameter family (Gamma-limit binomials, Straub's convention):
#   F(n1..n6) = sum_{k,j in Z} C(n1,k)C(n2,k)C(n3+k,k)C(n4,k+j)C(n5,k+j)C(n6+j,j).
# F(n,...,n)=a(n), F(-N,...,-N)=b(N-1).  Test F(p*n) ≡ F(n) (mod p^3) for random n in Z^6 with mixed signs, and p^{3r} for r=2 on the diagonal-ish.
import random
from math import comb
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def gbin(n,k):
    if k>=0 and n-k>=0: return comb(n,k)
    if n<0 and k>=0: return (-1)**k*comb(k-n-1,k)
    if n<0 and k<0 and n-k>=0: return (-1)**(n-k)*comb(-k-1,-n-1)
    return 0
def F(n,K=None):
    n1,n2,n3,n4,n5,n6=n
    B=max(abs(x) for x in n)*3+5
    tot=0
    for k in range(-B,B+1):
        t1=gbin(n1,k)*gbin(n2,k)*gbin(n3+k,k)
        if t1==0: continue
        for j in range(-B,B+1):
            t2=gbin(n4,k+j)*gbin(n5,k+j)*gbin(n6+j,j)
            if t2: tot+=t1*t2
    return tot
random.seed(1)
print("sanity: F(n,..,n)=a(n)?", [F((n,)*6) for n in range(5)])
for p in (5,7):
    res={'allpos':[], 'allneg':[], 'mixed':[]}
    for trial in range(40):
        kind=random.choice(list(res.keys()))
        if kind=='allpos': n=tuple(random.randint(1,4) for _ in range(6))
        elif kind=='allneg': n=tuple(-random.randint(1,4) for _ in range(6))
        else:
            n=tuple(random.choice([-1,1])*random.randint(1,4) for _ in range(6))
            if all(x>0 for x in n) or all(x<0 for x in n): continue
        pn=tuple(p*x for x in n)
        d=F(pn)-F(n)
        if F(pn)==F(n): continue
        res[kind].append(vp(d,p)-3)
    print(f"p={p}: slack vs p^3 by sign pattern:", {k:(min(v) if v else None, len(v)) for k,v in res.items()})
