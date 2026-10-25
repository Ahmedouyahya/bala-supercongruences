# Reduction of A361711 to a half-range harmonic-sum congruence at prime powers.
# Exact identities (to verify):  with n=(p^k-1)/2, n'=(p^(k-1)-1)/2, U = {0<u<p^k/2 : p∤u}
#   (E1) C(2n,n)/C(2n',n')      = (-1)^((p-1)/2) * prod_{u in U} (1 - p^k/u)
#   (E2) C(3n+1,n)/C(3n'+1,n')  = prod_{u in U} (1 + p^k/u)          [C(3n+1,n)=C(p^k+n,n)]
# Congruences (to test): q_k=(2^phi-1)/p^k, phi=p^k-p^(k-1)
#   (i)  H1 := sum_{u in U} 1/u  ==  -2 q_k + p^k q_k^2   (mod p^(2k))
#   (ii) H2 := sum_{u in U} 1/u^2 == 0 (mod p^k)
#   (W)  full-range sum_{0<u<p^k, p∤u} 1/u == 0 (mod p^(2k))
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
print(" p k | E1 E2 | v(i)-2k  v(ii)-k  v(W)-2k | v(H1 + 2q) [the simpler form H1 == -2q_k (mod p^?)]")
for p in (3,5,7,11,13,17,19,23,29,31,37,41,43,47):
    for k in (1,2,3,4):
        if p**k>60000: continue
        M,Mp=p**k,p**(k-1); n,n_=(M-1)//2,(Mp-1)//2; phi=M-Mp; q=Fraction(2**phi-1,M)
        U=[u for u in range(1,(M+1)//2) if u%p]
        P1=Fraction(1); P2=Fraction(1); H1=Fraction(0); H2=Fraction(0)
        for u in U:
            P1*=1-Fraction(M,u); P2*=1+Fraction(M,u); H1+=Fraction(1,u); H2+=Fraction(1,u*u)
        E1 = (Fraction(comb(2*n,n),comb(2*n_,n_)) == (-1)**((p-1)//2)*P1)
        E2 = (Fraction(comb(3*n+1,n),comb(3*n_+1,n_)) == P2)
        Hfull=sum(Fraction(1,u) for u in range(1,M) if u%p)
        print(f"{p:2d} {k} | {E1!s:5} {E2!s:5} | {vp(H1+2*q-M*q*q,p)-2*k:4d}  {vp(H2,p)-k:4d}  {vp(Hfull,p)-2*k:4d} | {vp(H1+2*q,p)}")
