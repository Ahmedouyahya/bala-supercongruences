# Class S first-order term  T_S = sum_{k',j'} S~(M;k',j') [H'_{pk'} + 2H'_{p(k'+j')} - H'_{pj'}]  must be ≡ 0 (mod p^{2r}).
# Split into the three pieces P1 (H'_{pk'}), P2 (2H'_{p(k'+j')}), P3 (-H'_{pj'}); stratify each by sigma = v_p(p x) of its harmonic index x in {k', k'+j', j'};
# report valuations of each stratum vs p^{2r}.  (Beukers' route: each stratum vanishes mod p^{2r}.)
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def vpint(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
for (p,r,m) in ((5,2,1),(5,2,2),(7,2,1),(5,3,1),(7,2,2),(11,2,1)):
    N=m*p**r; M=N//p
    Hp=[Fraction(0)]
    for i in range(1,N+2): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    St=lambda k,j: C(M-1,k)**2*C(M+k-1,k)*C(M-1,k+j)**2*C(M+j-1,j)
    P={1:{},2:{},3:{}}
    for k1 in range(M):
        for j1 in range(M-k1):
            s=St(k1,j1)
            if k1>0: P[1][vpint(p*k1,p)]=P[1].get(vpint(p*k1,p),0)+s*Hp[p*k1]
            if k1+j1>0: P[2][vpint(p*(k1+j1),p)]=P[2].get(vpint(p*(k1+j1),p),0)+2*s*Hp[p*(k1+j1)]
            if j1>0: P[3][vpint(p*j1,p)]=P[3].get(vpint(p*j1,p),0)-s*Hp[p*j1]
    tot=sum(sum(d.values()) for d in P.values())
    print(f"p={p} r={r} m={m}: v(T_S)-2r={vp(tot,p)-2*r:+d};  strata (piece: {{sigma: slack vs p^2r}}): "
          + "; ".join(f"P{i}: {{{', '.join(f'{sg}:{vp(v,p)-2*r:+d}' for sg,v in sorted(d.items()))}}}" for i,d in P.items()))
