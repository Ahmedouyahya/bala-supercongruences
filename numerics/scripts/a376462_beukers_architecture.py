# Beukers-style decomposition of a(N-1) - a(M-1), N = pM, M = m p^{r-1}, into harmonic-weighted level-M sums.
# Classes: S (p|k,p|j), K (p∤k,p|j), J (p|k,p∤j), B (p∤k,p∤j).  First-order models (exact mod N^2 relative to the leading factor).
# Predictions to check:
#   Sigma_K ≡ N (T0 - N T1)  (mod p^{3r}),   T0 = Σ'_k Σ_{j'} Psi(M;n',j')/k,  T1 = Σ'_k Σ_{j'} Psi(M;n',j') rho_K(k,j')/k,  need T0 ≡ 0 (p^{2r}), T1 ≡ 0 (p^r)
#   Sigma_J ≡ N (T0' - N T1')  similarly with Psi~ and rho_J
#   Sigma_B ≡ N^2 T_B0 (mod p^{3r}),   T_B0 = Σ'_{k,j} Xi(M;n',n'',delta)/(k j),  need T_B0 ≡ 0 (p^r)
#   Sigma_S ≡ a(M-1) - N T_S (mod p^{3r}),  T_S = Σ_{k',j'} S~(M;k',j') rho_S(k',j'),  need T_S ≡ 0 (p^{2r})
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
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def run(p,r,m):
    N=m*p**r; M=N//p
    # harmonic sums H'_n (p∤i, i<=n) up to 2N
    Hp=[Fraction(0)]
    for i in range(1,2*N+2): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    St=lambda L,k,j: C(L-1,k)**2*C(L+k-1,k)*C(L-1,k+j)**2*C(L+j-1,j)
    aM1=sum(St(M,k,j) for k in range(M) for j in range(M-k))
    SS=SK=SJ=SB=0
    T0=T1=Fraction(0); T0p=T1p=Fraction(0); TB0=Fraction(0); TS=Fraction(0)
    Psi=lambda n1,j1: C(M-1,n1)**2*C(M+n1,n1)*C(M-1,n1+j1)**2*C(M+j1-1,j1)
    Psit=lambda k1,n2: C(M-1,k1)**2*C(M+k1-1,k1)*C(M-1,k1+n2)**2*C(M+n2,n2)
    Xi=lambda n1,n2,d: C(M-1,n1)**2*C(M+n1,n1)*C(M-1,n1+n2+d)**2*C(M+n2,n2)
    for k in range(N):
        for j in range(N-k):
            t=St(N,k,j)
            if k%p==0 and j%p==0:
                SS+=t; k1,j1=k//p,j//p
                rhoS=Hp[k]+2*Hp[k+j]-Hp[j]
                TS+=St(M,k1,j1)*rhoS
            elif k%p and j%p==0:
                SK+=t; n1,j1=k//p,j//p
                rhoK=Hp[k]+Fraction(1,k)+2*Hp[k+j]-Hp[j]
                T0+=Fraction(Psi(n1,j1),k); T1+=Fraction(Psi(n1,j1),k)*rhoK
            elif k%p==0 and j%p:
                SJ+=t; k1,n2=k//p,j//p
                rhoJ=Hp[k]+2*Hp[k+j]-Hp[j]+Fraction(1,j)
                T0p+=Fraction(Psit(k1,n2),j); T1p+=Fraction(Psit(k1,n2),j)*rhoJ
            else:
                SB+=t; n1,n2=k//p,j//p; d=1 if (k%p)+(j%p)>=p else 0
                TB0+=Fraction(Xi(n1,n2,d),k*j)
    R=3*r
    print(f"p={p} r={r} m={m} (N={N}):")
    print(f"   class sums vs p^{{3r}}: S-a(M-1): {vp(SS-aM1,p)-R:+d}  K: {vp(SK,p)-R:+d}  J: {vp(SJ,p)-R:+d}  B: {vp(SB,p)-R:+d}")
    print(f"   model errors (need >=0): K: {vp(SK-N*(T0-N*T1),p)-R:+d}  J: {vp(SJ-N*(T0p-N*T1p),p)-R:+d}  B: {vp(SB-N*N*TB0,p)-R:+d}  S: {vp(SS-(aM1-N*TS),p)-R:+d}")
    print(f"   reduced sums: v(T0)-2r={vp(T0,p)-2*r:+d} v(T1)-r={vp(T1,p)-r:+d} | v(T0')-2r={vp(T0p,p)-2*r:+d} v(T1')-r={vp(T1p,p)-r:+d} | v(TB0)-r={vp(TB0,p)-r:+d} | v(TS)-2r={vp(TS,p)-2*r:+d}")
    sys.stdout.flush()
for (p,r,m) in ((5,2,1),(5,2,2),(7,2,1),(7,2,2),(11,2,1),(5,3,1)):
    run(p,r,m)
