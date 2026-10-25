# A370092 mod 2^e and mod p^e: minimal eventual period and start, vs phi and lambda. python -I numerics/a370092_powers_of_two.py
from math import comb
from fractions import Fraction
import sys
N=int(sys.argv[1]) if len(sys.argv)>1 else 1200
a=[Fraction(1)]
for n in range(1,N+1):
    s=sum((1-(-1)**j-(-2)**j)*comb(n,j)*a[n-j] for j in range(1,n+1)); a.append(Fraction((-1)**n)+Fraction(s,2))
assert all(x.denominator==1 for x in a); a=[int(x) for x in a]
def min_period(r):
    L=len(r)
    for P in range(1,L//3):
        # find smallest start st such that r[n+P]==r[n] for all n>=st
        st=L-P
        while st>0 and r[st-1+P]==r[st-1]: st-=1
        if st<=L//2: return P,st
    return None,None
def carmichael(pe):
    p,e=pe
    if p==2: return 1 if e==1 else (2 if e==2 else 2**(e-2))
    return (p-1)*p**(e-1)
print("modulus  minimal_period  start  phi  lambda  period|phi  period|lambda")
for p,emax in ((2,11),(3,6),(5,4),(7,3)):
    for e in range(1,emax+1):
        k=p**e; r=[x%k for x in a]; P,st=min_period(r)
        phi=(p-1)*p**(e-1); lam=carmichael((p,e))
        print(f"{p}^{e}={k:6d}  {P!s:>8}  {st!s:>5}  {phi:5d}  {lam:5d}  {P is not None and phi%P==0}  {P is not None and lam%P==0}")
# c_m = m! g_m where G(u)=(1+u)/(1-u^2-u^3/2): recurrence 2 g_m = 2 g_{m-2} + g_{m-3} (m>=2), g_0=g_1=1
g=[Fraction(1),Fraction(1)]
for m in range(2,80): g.append(g[m-2]+ (g[m-3]/2 if m>=3 else 0))
from math import factorial
def v2(x):
    if x==0: return 99
    v=0
    while x%2==0: x//=2; v+=1
    return v
c=[g[m]*factorial(m) for m in range(80)]
assert all(x.denominator==1 for x in c)
print("v2(c_m) for m=0..60:", [v2(int(c[m])) for m in range(61)])
print("v2(g_m) (negative = denominators):", [ -v2(g[m].denominator) if g[m].numerator%2 else v2(g[m].numerator) for m in range(31)])
# check a(n) == sum_m c_m S(n,m)
from sympy.functions.combinatorial.numbers import stirling
ok=all(a[n]==sum(int(c[m])*stirling(n,m) for m in range(n+1)) for n in range(0,40))
print("a(n)=sum c_m S(n,m) check:", ok)
