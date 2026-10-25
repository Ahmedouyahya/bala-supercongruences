# Which (a,b,c) satisfy the p^{3r} tower at p=3?  Direct exact test, v_3(A(m 3^r) - A(m 3^{r-1})) - 3r over m in {1,2,4}, r in {1,2,3} (N <= 108).
from fractions import Fraction
from math import comb
import sys
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def coeffs_pow(a,b,N,K):
    # [x^t] (1+x)^{aN} (1-x)^{bN}, t<=K, exact integers (generalized binomials for negative exponents)
    def gb(e,i):
        num=1
        for t in range(i): num*=(e-t)
        den=1
        for t in range(1,i+1): den*=t
        return num//den
    A=[gb(a*N,i) for i in range(K+1)]; B=[gb(b*N,i)*(-1)**i for i in range(K+1)]
    return [sum(A[i]*B[t-i] for i in range(t+1)) for t in range(K+1)]
def A(a,b,c,N): return coeffs_pow(a,b,N,c*N)[c*N]
p=3
cases=[(a,b,c) for c in (1,2,3) for a in range(-4,6) for b in range(-4,6) if (a,b)!=(0,0)]
hold=[];fail=[]
for (a,b,c) in cases:
    vals=[]
    for r in (1,2,3):
        for m in (1,2,4):
            N=m*p**r; M=m*p**(r-1)
            if c*N>330: continue
            d=A(a,b,c,N)-A(a,b,c,M)
            vals.append(vp(d,p)-3*r)
    mn=min(vals)
    (hold if mn>=0 else fail).append(((a,b,c),mn))
print("HOLD at p=3 (min slack over m in {1,2,4}, r<=3):")
for t,mn in hold: print("  ",t,"slack",mn)
print("FAIL count:",len(fail),"; examples:",fail[:12])
print("named: A002003 (1,-1,1):", [x for x in hold+fail if x[0]==(1,-1,1)], " A103885 (1,-1,2):",[x for x in hold+fail if x[0]==(1,-1,2)], " A119259 (2,-1,1):",[x for x in hold+fail if x[0]==(2,-1,1)], " A352373 (-1,-3,1):",[x for x in hold+fail if x[0]==(-1,-3,1)])
