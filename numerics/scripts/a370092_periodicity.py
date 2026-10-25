# Test: A370092 mod k eventually periodic with period | phi(k)?  (python -I a370092_periodicity.py 400 40)
import sys
from math import comb
from fractions import Fraction
from sympy import totient
N=int(sys.argv[1]) if len(sys.argv)>1 else 400; KMAX=int(sys.argv[2]) if len(sys.argv)>2 else 40
a=[Fraction(1)]
for n in range(1,N+1):
    s=sum((1-(-1)**j-(-2)**j)*comb(n,j)*a[n-j] for j in range(1,n+1)); a.append(Fraction((-1)**n)+Fraction(s,2))
assert all(x.denominator==1 for x in a); a=[int(x) for x in a]
def period(seq,k):
    r=[x%k for x in seq]; L=len(r)
    for P in range(1,L//3):
        for st in range(0,L//2):
            if all(r[n+P]==r[n] for n in range(st,L-P)): return P,st
    return None,None
for k in range(3,KMAX+1):
    P,st=period(a,k); phi=int(totient(k)); print(f"k={k} period={P} start={st} phi={phi} ok={P is not None and phi%P==0}")
