# p=3, (a,b,c)=(2,-1,1) [A119259]: where does the aggregate cancellation E2+E3 == 0 mod 3^{3r} happen? group the s-sum by blocks.
from fractions import Fraction
from math import factorial
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
def coeffs(a,b,N,K):
    A=[gbinom(a*N,i) for i in range(K+1)]; B=[gbinom(b*N,i)*(-1)**i for i in range(K+1)]
    return [sum(A[i]*B[s-i] for i in range(s+1)) for s in range(K+1)]
def L_coeffs(a,b,p,K): return [Fraction(0)]+[ (Fraction(a*(-1)**(j+1),j)-Fraction(b,j)) if j%p else Fraction(0) for j in range(1,K+1)]
def mul(A,B,K):
    R=[Fraction(0)]*(K+1)
    for i,x in enumerate(A):
        if x==0: continue
        for j,y in enumerate(B):
            if i+j>K: break
            R[i+j]+=x*y
    return R
p=3; a,b,c=2,-1,1
for r in (1,2,3):
    for m in (1,2):
        M=m*p**(r-1); N=p*M; K=p*c*M
        gam=coeffs(a,b,M,c*M); L=L_coeffs(a,b,p,K); L2=mul(L,L,K); L3=mul(L2,L,K)
        terms=[gam[s]*(Fraction(N**2,2)*L2[p*(c*M-s)]+Fraction(N**3,6)*L3[p*(c*M-s)]) for s in range(0,c*M)]
        tot=sum(terms)
        # valuations of individual terms and of block sums over s in blocks of length p, p^2
        tv=[vp(t,p)-3*r for t in terms]
        blocks_p=[vp(sum(terms[s] for s in range(b0,min(b0+p,c*M))),p)-3*r for b0 in range(0,c*M,p)]
        # pairing s <-> cM-1-s ?
        pairs=[vp(terms[s]+terms[c*M-1-s],p)-3*r for s in range(0,(c*M)//2)]
        print(f"r={r} m={m}: v(E2+E3)-3r={vp(tot,p)-3*r}; termwise min={min(tv)}; p-block sums min={min(blocks_p)}; pair(s,cM-1-s) min={min(pairs) if pairs else None}")
