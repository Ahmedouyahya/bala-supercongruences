# Class J (p | k, p ∤ j): mirror of class K with kernel Phi_s(k,j) = C(L_s-1,k)^2 C(-L_s,k)(-1)^k C(L_s-1,k+j)^2 C(-L_s-1,j)(-1)^j,
# K'_s(j) = sum_k Phi_s(k,j), A'_s = sum_{j<L_s} sigma_{r-s}(j) K'_s(j); step pieces X1' (-H'_j), X2' (+H'_{pk''}), X3' (2H'_{pk''+j})  [rho' = -H'_j + H'_{pk1} + 2H'_{j+pk1}], Y' (carry, 1/k weights).
from math import comb
from fractions import Fraction
import sys
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b):
    if b<0: return 0
    if a>=0: return comb(a,b) if b<=a else 0
    return (-1)**b*comb(b-a-1,b)
def run(p,r,m):
    N=m*p**r
    Hp=[Fraction(0)]
    for i in range(1,N+2): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    def sigma(t,n): return sum(Fraction(1,k) for k in range(n*p**t,(n+1)*p**t) if k%p and k>0)
    def Phi(s,k,j):
        L=m*p**s
        if k+j>L-1: return 0
        return C(L-1,k)**2*C(-L,k)*(-1)**k*C(L-1,k+j)**2*C(-L-1,j)*(-1)**j
    def Kp(s,j): return sum(Phi(s,k,j) for k in range(0,m*p**s-j))
    def XiJ(s,q1,q,d):  # kernel for unscaled-k terms: C(L-1,k)^2 C(-L-1,k-1)... reduced: q1=[k/p], q=[j/p]
        L=m*p**s
        return C(L-1,q1)**2*C(-L-1,q1)*(-1)**q1*C(L-1,q1+q+d)**2*C(-L-1,q)*(-1)**q
    A={}
    for s in range(0,r):
        A[s]=sum(sigma(r-s,j)*Kp(s,j) for j in range(m*p**s))
    classJ=sum(Fraction(N,j)/(1+Fraction(N,j))*Phi(r,p*k1,j) for j in range(1,N) if j%p for k1 in range(0,(N-1-j)//p+1))
    top=sum(Fraction(1,j)*sum(Phi(r,p*k1,j) for k1 in range(0,(N-1-j)//p+1)) for j in range(1,N) if j%p)
    Xhat=Fraction(0)
    for j in range(1,N):
        if j%p==0: continue
        n2=j//p
        for k1 in range(0,m*p**(r-1)-n2):
            rho=-Hp[j]+Hp[p*k1]+2*Hp[j+p*k1]
            Xhat+=Fraction(1,j)*Phi(r-1,k1,n2)*rho
    print(f"p={p} r={r} m={m}: A'_s slack: {[vp(A[s],p)-2*r for s in range(r)]}; top err {vp(top-(A[r-1]-N*Xhat),p)-2*r:+d}; v(Xhat')-r {vp(Xhat,p)-r:+d}; classJ slack {vp(classJ,p)-3*r:+d}")
    for s in range(0,r-1):
        Ls1=m*p**(s+1); Ls=m*p**s
        X1=X2=X3=Fraction(0); Y={0:Fraction(0),1:Fraction(0)}
        for j in range(Ls1):
            sg=sigma(r-s-1,j); q=j//p; v=j%p
            for k2 in range(0,Ls-q):
                Pq=Phi(s,k2,q)
                if Pq==0: continue
                X1+=sg*Pq*(-Hp[j]); X2+=sg*Pq*Hp[p*k2]; X3+=sg*Pq*2*Hp[j+p*k2]
            for k in range(1,Ls1-j):
                if k%p==0: continue
                q1=k//p; u=k%p; d=1 if u+v>=p else 0
                Y[d]+=sg*Fraction(1,k)*XiJ(s,q1,q,d)
        lhs=A[s+1]-A[s]; rhs=-m*p**(s+1)*(X1+X2+X3+Y[0]+Y[1]); tgt=2*r-s-1
        print(f"   step {s}->{s+1}: identity err {vp(lhs-rhs,p)-2*r:+d}; pieces: X1' {vp(X1,p)-tgt:+d} X2' {vp(X2,p)-tgt:+d} X3' {vp(X3,p)-tgt:+d} Y0' {vp(Y[0],p)-tgt:+d} Y1' {vp(Y[1],p)-tgt:+d}")
    sys.stdout.flush()
for (p,r,m) in ((5,2,1),(5,2,2),(7,2,1),(5,3,1)):
    run(p,r,m)
