# Theorem F at p=3: split A(N)-A(M) = sum_s gamma_s * eps_{p(cM-s)} into the j=2 (quadratic), j=3 (cubic), j>=4 parts of exp(N L)-1 and
# measure their 3-adic valuations, for instances that hold numerically at p=3 (A119259 (2,-1,1), A333561 (3,-1,2), A333562 (4,-1,3)) and one that fails (A352373 (-1,-3,1)).
from fractions import Fraction
from math import factorial
import sys
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def gbinom(a,k):
    num=1
    for i in range(k): num*=(a-i)
    den=1
    for i in range(1,k+1): den*=i
    return Fraction(num,den)
def series_pow_coeffs(a,b,N,K):  # coefficients of (1+y)^{aN}(1-y)^{bN} up to y^K
    A=[gbinom(a*N,i) for i in range(K+1)]; B=[gbinom(b*N,i)*(-1)**i for i in range(K+1)]
    return [sum(A[i]*B[s-i] for i in range(s+1)) for s in range(K+1)]
def L_coeffs(a,b,p,K):  # L = aV - bU, coefficient of x^j: a(-1)^(j+1)/j - b/j for p∤j, else 0
    return [Fraction(0)]+[ (Fraction(a*(-1)**(j+1),j)-Fraction(b,j)) if j%p else Fraction(0) for j in range(1,K+1)]
def mul(A,B,K):
    R=[Fraction(0)]*(K+1)
    for i,x in enumerate(A):
        if x==0: continue
        for j,y in enumerate(B):
            if i+j>K: break
            R[i+j]+=x*y
    return R
p=3
for (a,b,c,name) in ((2,-1,1,'A119259'),(3,-1,2,'A333561'),(4,-1,3,'A333562'),(-1,-3,1,'A352373')):
    for r in (1,2):
        for m in (1,2):
            M=m*p**(r-1); N=p*M; K=p*c*M
            gam=series_pow_coeffs(a,b,M,c*M)
            L=L_coeffs(a,b,p,K)
            Lj=[None,L]; 
            for j in range(2,8): Lj.append(mul(Lj[-1],L,K))
            parts={}
            for j in range(2,8):
                parts[j]=sum(gam[s]*Fraction(N**j,factorial(j))*Lj[j][p*(c*M-s)] for s in range(0,c*M))
            total=sum(parts.values())
            # exact A(N)-A(M)
            AN=series_pow_coeffs(a,b,N,c*N)[c*N]; AM=gam[c*M]
            print(f"{name} r={r} m={m}: v3(A(N)-A(M))-3r={vp(AN-AM,p)-3*r}; parts(j=2..7) v3-3r: {[vp(parts[j],p)-3*r for j in range(2,8)]}; v3(E2+E3)-3r={vp(parts[2]+parts[3],p)-3*r}; v3(sum parts)-3r={vp(total,p)-3*r}; identity sum==A(N)-A(M): {total==AN-AM}")
