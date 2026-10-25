# Multivariate extension of A376462 in Straub's style: A(n1..n5; d) = ct[ (1+u+v)^{n1} (1+z)^{n2} (1+u+z)^{n3} (1+w)^{n4} (1+v+w)^{n5} / (u^{d1} v^{d2} z^{d3} w^{d4}) ].
# As a finite sum: expand each factor by multinomials. Test A(p n) == A(n) mod p^3 for several integer vectors n (including negative entries, via generalized binomials),
# and the diagonal/shift relation to a(n-1).
from math import comb
from fractions import Fraction
from itertools import product
def gb(a,k):  # generalized binomial C(a,k) for integer a, k>=0
    if k<0: return 0
    num=1
    for i in range(k): num*=(a-i)
    den=1
    for i in range(1,k+1): den*=i
    return num//den
def mult3(n,i,j):  # coefficient of u^i v^j in (1+u+v)^n  = C(n,i) C(n-i,j)  (generalized, n may be negative)
    return gb(n,i)*gb(n-i,j)
def A(n1,n2,n3,n4,n5,d,K=None):
    # (1+u+v)^{n1}: u^i1 v^j1 ; (1+z)^{n2}: z^k2 ; (1+u+z)^{n3}: u^i3 z^k3 ; (1+w)^{n4}: w^l4 ; (1+v+w)^{n5}: v^j5 w^l5
    # constraints: i1+i3=d1 ; j1+j5=d2 ; k2+k3=d3 ; l4+l5=d4.   Finite when d>=0 (nonnegative exponents only).
    d1,d2,d3,d4=d; s=0
    for i1 in range(d1+1):
        i3=d1-i1
        for j1 in range(d2+1):
            j5=d2-j1
            c1=mult3(n1,i1,j1)
            if c1==0: continue
            for k3 in range(d3+1):
                k2=d3-k3
                c3=mult3(n3,i3,k3); c2=gb(n2,k2)
                if c3==0 or c2==0: continue
                for l5 in range(d4+1):
                    l4=d4-l5
                    s+=c1*c2*c3*gb(n4,l4)*mult3(n5,j5,l5)
    return s
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
print("diagonal check A(n,n,n,n,n;(n,n,n,n)) = a(n):", all(A(n,n,n,n,n,(n,n,n,n))==a(n) for n in range(0,7)))
# does a(n-1) arise from negative indices? try A(-n,-n,-n,-n,-n; d) for small d patterns
print("A(-n,...,-n;(n-1,n-1,n-1,n-1)) vs a(n-1):", [(A(-n,-n,-n,-n,-n,(n-1,)*4), a(n-1)) for n in range(1,6)])
print("A(-n,...,-n;(n,n,n,n)) vs a(n-1), a(n):", [(A(-n,-n,-n,-n,-n,(n,)*4), a(n-1), a(n)) for n in range(1,6)])
# multivariate supercongruence tests mod p^3 (r=1): A(p n; p d) vs A(n; d)
import random
random.seed(7)
for p in (5,7):
    worst=99; tests=0
    for _ in range(14):
        n=[random.choice([-3,-2,-1,1,2,3]) for _ in range(5)]; d=[random.randint(0,2) for _ in range(4)]
        hi=A(*[p*x for x in n], tuple(p*x for x in d)); lo=A(*n, tuple(d))
        if hi==lo: continue
        tests+=1; worst=min(worst, vp(hi-lo,p)-3)
    print(f"p={p}: random multivariate A(pn;pd) vs A(n;d), {tests} nontrivial tests, min slack vs p^3 = {worst}")
