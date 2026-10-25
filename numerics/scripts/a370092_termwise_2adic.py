# Termwise test for A370092 mod 2^e: b_k = k!(S(n+P,k)-S(n,k)) with P=2^(e-1); does v2(b_k)+v2(g_k) >= e hold for every k?
from fractions import Fraction
from math import factorial, comb
import sys
from sympy.functions.combinatorial.numbers import stirling
def v2(x):
    x=Fraction(x)
    if x==0: return 99
    n,d=x.numerator,x.denominator; v=0
    while n%2==0: n//=2; v+=1
    while d%2==0: d//=2; v-=1
    return v
g=[Fraction(1),Fraction(1)]
for m in range(2,70): g.append(g[m-2]+(g[m-3]/2 if m>=3 else 0))
n0=int(sys.argv[1]) if len(sys.argv)>1 else 120
for e in range(3,10):
    P=2**(e-1); worst=99; worst_k=None; tot=Fraction(0); bad=[]
    for k in range(0,66):
        bk=factorial(k)*(stirling(n0+P,k)-stirling(n0,k))
        tot+=bk*g[k]
        if bk==0: continue
        slack=v2(bk)+v2(g[k])-e
        if slack<0: bad.append((k,v2(bk)-(e+1),v2(g[k]),slack))
        if slack<worst: worst=slack; worst_k=k
    print(f"e={e} P={P} n={n0}: v2(total)-e = {v2(tot)-e}; worst termwise slack {worst} at k={worst_k}; termwise failures (k, v2(b_k)-(e+1), v2(g_k), slack): {bad}")
# profile of v2(b_k)-(e+1) vs k for one e
e=7; P=2**(e-1)
print("e=7 profile k: v2(b_k)-(e+1), v2(g_k), v2(floor(k/2)!) :")
print([(k, v2(factorial(k)*(stirling(n0+P,k)-stirling(n0,k)))-(e+1), v2(g[k]), v2(factorial(k//2))) for k in range(0,40)])
