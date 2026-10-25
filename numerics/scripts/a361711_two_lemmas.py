# A361711 at odd M=2n+1: a(M) = (-1)^n C(3n+1,n) C(2n,n). Test the two prime-power Morley-type lemmas:
#  Lemma M : C(2n,n)   == (-1)^((p-1)/2) * 4^(phi)  * C(2n',n')   (mod p^(3k)),  n=(p^k-1)/2, n'=(p^(k-1)-1)/2, phi=p^k-p^(k-1)
#  Lemma M3: C(3n+1,n) == 4^(-phi) * C(3n'+1,n')                   (mod p^(3k))
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def a361711(M):
    if M==1: return 1
    return sum((-1)**k*comb(M,k)**2*comb(M-2,k) for k in range(0,M-1))
print("closed form a(2n+1)=(-1)^n C(3n+1,n)C(2n,n):", all(a361711(2*n+1)==(-1)**n*comb(3*n+1,n)*comb(2*n,n) for n in range(0,30)))
print("p  k | v_p(LemmaM) v_p(LemmaM3) v_p(a(p^k)-a(p^(k-1)))  [need >= 3k]")
for p in (5,7,11,13,17,19,23,29,31,37,41,43):
    for k in (1,2,3,4):
        if p**k>20000: continue
        M,Mp=p**k,p**(k-1); n,n_=(M-1)//2,(Mp-1)//2; phi=M-Mp; sgn=(-1)**((p-1)//2)
        LM=vp(Fraction(comb(2*n,n),comb(2*n_,n_))-sgn*Fraction(4)**phi,p)
        LM3=vp(Fraction(comb(3*n+1,n),comb(3*n_+1,n_))-Fraction(4)**(-phi),p)
        full=vp((-1)**n*comb(3*n+1,n)*comb(2*n,n)-(-1)**n_*comb(3*n_+1,n_)*comb(2*n_,n_),p)
        print(f"{p:3d} {k} | {LM:3d} {LM3:3d} {full:3d}   3k={3*k}")
