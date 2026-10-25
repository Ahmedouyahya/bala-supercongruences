# Second conjectured congruence for A376462: a(mp^r - 1) == a(mp^(r-1) - 1) mod p^(3r). Structure probe.
# a(N-1) = sum_{k,i} C(N-1,k)^2 C(N-1+k,k) C(N-1,i)^2 C(2N-2-k-i, N-1).
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def T1(n,k,i): return C(n,k)**2*C(n+k,k)*C(n,i)**2*C(2*n-k-i,n)
for p in (5,7):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            if N>250: continue
            n1,n2=N-1,M-1
            tot=sum(T1(n1,k,i) for k in range(n1+1) for i in range(n1+1))-sum(T1(n2,k,i) for k in range(n2+1) for i in range(n2+1))
            # classes by k mod p and i mod p at the upper level; natural pairing: k <-> ? try k' = (k - (p-1)) / p i.e. k == p-1 mod p scaled?
            cls={}
            for k in range(n1+1):
                for i in range(n1+1):
                    key=(k%p==p-1, i%p==p-1)   # indices congruent to -1 mod p correspond to scaled lower-level indices k'=(k+1)/p-1
                    cls[key]=cls.get(key,0)+T1(n1,k,i)
            # lower-level matching: k=p k'+p-1 <-> k'
            matched=sum(T1(n1,p*k+p-1,p*i+p-1)-T1(n2,k,i) for k in range(n2+1) for i in range(n2+1))
            tw=min((vp(T1(n1,p*k+p-1,p*i+p-1)-T1(n2,k,i),p) for k in range(n2+1) for i in range(n2+1) if T1(n1,p*k+p-1,p*i+p-1)-T1(n2,k,i)),default=999)
            print(f"p={p} r={r} m={m}: v(a(N-1)-a(M-1))-3r={vp(tot,p)-3*r}; matched(-1 classes) diff {vp(matched,p)-3*r} termwise {tw-3*r}; other classes: "+", ".join(f"{k}:{vp(v,p)-3*r}" for k,v in cls.items() if k!=(True,True)))
