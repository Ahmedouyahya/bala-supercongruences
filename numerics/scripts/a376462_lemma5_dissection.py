# Beukers Lemma-5-type induction for the class-K sum of A376462 (shifted), general framework:
#   L_s = m p^s;  Psi_s(n,j) = C(L_s-1,n)^2 C(-L_s-1,n)(-1)^n C(L_s-1,n+j)^2 C(-L_s,j)(-1)^j   (n+j <= L_s-1)
#   K_s(n) = sum_j Psi_s(n,j);   sigma_t(n) = sum'_{[k/p^t]=n} 1/k;   A_s = sum_{n<L_s} sigma_{r-s}(n) K_s(n)   (s <= r-1)
#   Top: Khat_r(k) = sum_{j'} Psi_r(k, p j');  class-K sum = N sum'_k (1/k)(1+N/k)^{-1} Khat_r(k).
# Step prediction:  A_{s+1} - A_s ≡ -m p^{s+1} (X_s + Y_s) (mod p^{2r}),
#   X_s = sum_{n<L_{s+1}} sigma_{r-s-1}(n) sum_{j''} Psi_s(q,j'') rho_s(n,j''),  q=[n/p], rho_s = H'_n - H'_{pj''} + 2 H'_{n+pj''}
#   Y_s = sum_n sigma_{r-s-1}(n) sum'_{j} (1/j) Xi_s^{(delta)}(q,[j/p]),  Xi_s^{(d)}(q,q') = C(L_s-1,q)^2 C(-L_s-1,q)(-1)^q C(L_s-1,q+q'+d)^2 C(-L_s-1,q')(-1)^{q'}  [sign to be checked numerically]
# We check the step identity and report valuations of the pieces X1 (H'_n part), X2 (-H'_{pj''} part), X3 (2H'_{n+pj''} part), Y (by delta) relative to the target 2r-s-1.
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
    # generalized binomial for integer a (possibly negative), b>=0
    if b<0: return 0
    if a>=0: return comb(a,b) if b<=a else 0
    return (-1)**b*comb(b-a-1,b)
def run(p,r,m):
    N=m*p**r
    Hp=[Fraction(0)]
    for i in range(1,N+2): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    def sigma(t,n):  # sum' over k in [n p^t, (n+1)p^t) of 1/k
        return sum(Fraction(1,k) for k in range(n*p**t,(n+1)*p**t) if k%p and k>0)
    def Psi(s,n,j):
        L=m*p**s
        if n+j>L-1: return 0
        return C(L-1,n)**2*C(-L-1,n)*(-1)**n*C(L-1,n+j)**2*C(-L,j)*(-1)**j
    def K(s,n): return sum(Psi(s,n,j) for j in range(0,m*p**s-n))
    def Xi(s,q,q1,d):
        L=m*p**s
        return C(L-1,q)**2*C(-L-1,q)*(-1)**q*C(L-1,q+q1+d)**2*C(-L-1,q1)*(-1)**q1
    print(f"p={p} r={r} m={m}:")
    A={}
    for s in range(0,r):
        A[s]=sum(sigma(r-s,n)*K(s,n) for n in range(m*p**s))
        print(f"  v(A_{s})-2r = {vp(A[s],p)-2*r:+d}")
    # top level: class K sum vs N*(A_{r-1} - N*Xhat) ; also the exact class-K sum
    classK=0
    for k in range(1,N):
        if k%p==0: continue
        for j1 in range(0,(N-1-k)//p+1):
            classK+=Fraction(N,k)/(1+Fraction(N,k))*Psi(r,k,p*j1)
    Xhat=Fraction(0)
    for k in range(1,N):
        if k%p==0: continue
        n1=k//p
        for j1 in range(0,m*p**(r-1)-n1):
            rho=Hp[k]-Hp[p*j1]+2*Hp[k+p*j1]
            Xhat+=Fraction(1,k)*Psi(r-1,n1,j1)*rho
    top=sum(Fraction(1,k)*sum(Psi(r,k,p*j1) for j1 in range(0,(N-1-k)//p+1)) for k in range(1,N) if k%p)
    print(f"  top: v(sum'(1/k)Khat_r - (A_{r-1} - N Xhat)) - 2r = {vp(top-(A[r-1]-N*Xhat),p)-2*r:+d};  v(Xhat)-r = {vp(Xhat,p)-r:+d};  v(classK) - 3r = {vp(classK,p)-3*r:+d}")
    # steps s -> s+1 for s = 0..r-2
    for s in range(0,r-1):
        Ls1=m*p**(s+1); Ls=m*p**s
        X1=X2=X3=Fraction(0); Y={0:Fraction(0),1:Fraction(0)}
        for n in range(Ls1):
            sg=sigma(r-s-1,n); q=n//p; u=n%p
            for j2 in range(0,Ls-q):
                Pq=Psi(s,q,j2)
                if Pq==0: continue
                X1+=sg*Pq*Hp[n]; X2+=sg*Pq*(-Hp[p*j2]); X3+=sg*Pq*2*Hp[n+p*j2]
            for j in range(1,Ls1-n):
                if j%p==0: continue
                q1=j//p; v=j%p; d=1 if u+v>=p else 0
                Y[d]+=sg*Fraction(1,j)*Xi(s,q,q1,d)
        lhs=A[s+1]-A[s]; rhs=-m*p**(s+1)*(X1+X2+X3+Y[0]+Y[1])
        tgt=2*r-s-1
        print(f"  step {s}->{s+1}: v(A_{s+1}-A_s + m p^(s+1)(X+Y)) - 2r = {vp(lhs-rhs,p)-2*r:+d} | pieces vs p^{{2r-s-1}}: X1 {vp(X1,p)-tgt:+d}, X2 {vp(X2,p)-tgt:+d}, X3 {vp(X3,p)-tgt:+d}, Y0 {vp(Y[0],p)-tgt:+d}, Y1 {vp(Y[1],p)-tgt:+d}, X2+X3 {vp(X2+X3,p)-tgt:+d}, X+Y {vp(X1+X2+X3+Y[0]+Y[1],p)-tgt:+d}")
        sys.stdout.flush()
for (p,r,m) in ((5,2,1),(5,2,2),(7,2,1),(5,3,1),(7,2,2)):
    run(p,r,m)
