# Sub-conjecture from the r=2 dissection of class K: mu(M) := sum_{n'<M} (2n'+1) Psi(M,n') ≡ 0 (mod p^2) for M = m p,
# Psi(M,n') = C(M-1,n')^2 C(M+n',n') sum_{j'} C(M-1,n'+j')^2 C(M+j'-1,j').  Also list moment valuations.
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def Psi(M,n1): return C(M-1,n1)**2*C(M+n1,n1)*sum(C(M-1,n1+j1)**2*C(M+j1-1,j1) for j1 in range(0,M))
for p in (5,7,11,13):
    for m in (1,2,3):
        M=m*p
        mom=[sum(Psi(M,n1)*n1**t for n1 in range(M)) for t in range(4)]
        extra='-'
        if p<=7 and m==1:
            M2=p*p; mm=[sum(Psi(M2,n1)*n1**t for n1 in range(M2)) for t in range(2)]
            extra=vp(mm[0]+2*mm[1],p)
        print(f"p={p} M={M}: v(m0)={vp(mom[0],p)} v(m1)={vp(mom[1],p)} v(m0+2m1)={vp(mom[0]+2*mom[1],p)} v(m2)={vp(mom[2],p)} v(m3)={vp(mom[3],p)} | v(m0+2m1) at M=p^2: {extra}")
