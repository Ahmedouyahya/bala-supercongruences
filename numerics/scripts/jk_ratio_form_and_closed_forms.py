# (1) Jacobsthal-Kazandzidis RATIO form test: v_p( C(pa,pb)/C(a,b) - 1 ) >= 3 + v_p(a)+v_p(b)+v_p(a-b), p>=5
# (2) A361711 closed forms for all n (odd and even) vs the defining sum
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
for p in (5,7,11):
    worst=99; cnt=0; where=None
    for a in range(1,61):
        for b in range(1,a):
            lhs=vp(Fraction(comb(p*a,p*b),comb(a,b))-1,p); rhs=3+vp(a,p)+vp(b,p)+vp(a-b,p)
            cnt+=1
            if lhs-rhs<worst: worst=lhs-rhs; where=(a,b,lhs,rhs)
    print(f"p={p}: {cnt} pairs, min(v_p(ratio-1) - (3+v(a)+v(b)+v(a-b))) = {worst} at (a,b,lhs,rhs)={where}")
# level form used in the A386548 argument: p^s | A, p^s | B  =>  C(pA,pB)/C(A,B) == 1 mod p^(3(s+1))
for p in (5,7):
    worst=99
    for s in (0,1,2):
        for A in range(p**s, 40*p**s+1, p**s):
            for B in range(p**s, A, p**s):
                worst=min(worst, vp(Fraction(comb(p*A,p*B),comb(A,B))-1,p)-3*(s+1))
    print(f"p={p}: level form min slack = {worst}")
def a361711(N):
    if N==1: return 1
    return sum((-1)**k*comb(N,k)**2*comb(N-2,k) for k in range(0,N-1))
odd_ok=all(a361711(2*n+1)==(-1)**n*comb(3*n+1,n)*comb(2*n,n) for n in range(0,60))
even_ok=all(a361711(2*n)==(-1)**n*Fraction(1,6)*Fraction(2*n-3,2*n-1)*Fraction(comb(3*n,n)*comb(2*n,n)) for n in range(1,60))
print("A361711 closed forms: odd N (n<=59):",odd_ok," even N (OEIS formula, n=1..59):",even_ok)
# also: is a(np^k) == a(np^(k-1)) mod p^(3k) for odd n>1 ? (not conjectured; curiosity)
for p in (5,7):
    print(f"p={p} odd n>1:", [(n,k,vp(a361711(n*p**k)-a361711(n*p**(k-1)),p)) for n in (3,5,7) for k in (1,2) if n*p**k<400])
