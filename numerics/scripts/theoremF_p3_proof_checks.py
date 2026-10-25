# Numerical verification of every step of the p=3 proof (Theorem F_3).
# Notation: phi=(1+x)^a(1-x)^b, A(N)=[x^{cN}]phi^N, N=3M, M=3^{r-1}m, L=sum_{3∤i} l_i x^i/i, l_i=a(-1)^{i+1}-b, psi = x phi'/phi = sum_{i>=1} l_i x^i,
# C = 3-section (Cartier), lambda_M(f) = [y^{cM}] phi(y)^M f(y), g = D^{-1} C(L^2) = sum_t ([x^{3t}]L^2 / t) y^t.
# (V1) A(N)-A(M) ≡ (9 M^3/2) * lambda_M( L - (psi-c) g )   (mod 3^{3r})  for ALL (a,b,c)   [this also gives the weak bound 3^{3r-1}]
# (V2) g_t ∈ Z_(3) and g_t ≡ a^2 (-1)^t + b^2 (mod 3)
# (V3) F_3-identity: L ≡ (psi - c)(g + K0) (mod 3) with K0 = 0 if 3∤c and a+b≡c; K0 = 1 if 3|c, a≢b; K0 = 2 if 3|c, a≡b≢0; and it FAILS for other classes.
# (V4) lambda_M(psi - c) = 0 exactly.
from fractions import Fraction
from math import comb
P=3
def vp(x):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%P==0: a//=P; v+=1
    while b%P==0: b//=P; v-=1
    return v
def mod3(x):
    x=Fraction(x); assert x.denominator%P, x
    return (x.numerator*pow(x.denominator,-1,P))%P
def gb(e,i):
    num=1
    for t in range(i): num*=(e-t)
    den=1
    for t in range(1,i+1): den*=t
    return Fraction(num,den)
def phi_pow(a,b,E,K):
    A=[gb(a*E,i) for i in range(K+1)]; B=[gb(b*E,i)*(-1)**i for i in range(K+1)]
    return [sum(A[i]*B[t-i] for i in range(t+1)) for t in range(K+1)]
def mul(f,g,K):
    h=[Fraction(0)]*(K+1)
    for i,x in enumerate(f):
        if x==0: continue
        for j,y in enumerate(g):
            if i+j>K: break
            h[i+j]+=x*y
    return h
def Lser(a,b,K): return [Fraction(0)]+[Fraction(a*(-1)**(i+1)-b,i) if i%P else Fraction(0) for i in range(1,K+1)]
def psiser(a,b,K): return [Fraction(0)]+[Fraction(a*(-1)**(i+1)-b) for i in range(1,K+1)]
bad1=0; tested=0; weak_ok=True
pairs=[(2,-1),(3,-1),(4,-1),(-1,-3),(1,-1),(0,1),(1,0),(2,2),(0,2),(1,1),(1,2),(-4,3),(5,2),(3,3),(-3,1),(4,4)]
print("(V1) reduction check: v3(A(N)-A(M) - (9M^3/2) lambda_M(L-(psi-c)g)) - 3r  [need >=0], and v3(A(N)-A(M))-3r:")
for c in (1,2,3):
    for (a,b) in pairs:
        row=[]
        for r in (1,2,3):
            for m in (1,2):
                M=m*P**(r-1); N=P*M
                if c*N>250: continue
                K=c*N
                L=Lser(a,b,K); L2=mul(L,L,K)
                cM=c*M
                g=[Fraction(0)]+[L2[P*t]/t for t in range(1,cM+1)]
                psi=psiser(a,b,cM)
                f=[L[t]-sum((psi[i]-(c if i==0 else 0))*g[t-i] for i in range(0,t+1)) for t in range(cM+1)]  # L - (psi-c) g, truncated at cM
                gam=phi_pow(a,b,M,cM)
                lam=sum(gam[s]*f[cM-s] for s in range(cM+1))
                AN=phi_pow(a,b,N,K)[K]; AM=gam[cM]
                diff=AN-AM-Fraction(9*M**3,2)*lam
                v=vp(diff)-3*r; tested+=1
                if v<0: bad1+=1
                if vp(AN-AM)<3*r-1: weak_ok=False
                row.append(f"r{r}m{m}:{v:+d}/{vp(AN-AM)-3*r:+d}")
        print(f"  (a,b,c)=({a},{b},{c}) a+b-c mod3={(a+b-c)%3}: "+" ".join(row))
print("(V1) failures:",bad1,"of",tested,"; weak bound 3^{3r-1} always holds:",weak_ok)
print("(V2) g integrality and residues:")
for (a,b) in pairs[:8]:
    K=3*200; L=Lser(a,b,K); L2=mul(L,L,K)
    gt=[L2[3*t]/t for t in range(1,201)]
    ok_int=all(vp(x)>=0 for x in gt); ok_res=all(mod3(gt[t-1])==(a*a*(-1)**t+b*b)%3 for t in range(1,201))
    print(f"  (a,b)=({a},{b}): integral {ok_int}, g_t ≡ a^2(-1)^t+b^2: {ok_res}")
print("(V3) F_3 identity L ≡ (psi-c)(gbar+K0):")
def K0_of(a,b,c):
    if c%3: return 0 if (a+b-c)%3==0 else None
    if (a-b)%3: return 1
    if a%3: return 2
    return 0
K=120
allok=True
for c in (0,1,2):
    for a in range(3):
        for b in range(3):
            l=[0]+[((a*(-1)**(i+1)-b)*pow(i,-1,3))%3 if i%3 else 0 for i in range(1,K+1)]
            psi=[0]+[(a*(-1)**(i+1)-b)%3 for i in range(1,K+1)]
            gbar=[0]+[(a*a*(-1)**t+b*b)%3 for t in range(1,K+1)]
            k0=K0_of(a,b,c)
            best=None
            for kk in range(3):
                h=[(gbar[t]+(kk if t==0 else 0))%3 for t in range(K+1)]
                u=[(psi[t]-(c if t==0 else 0))%3 for t in range(K+1)]
                prod=[sum(u[i]*h[t-i] for i in range(t+1))%3 for t in range(K+1)]
                if prod==l: best=kk
            predicted = ("none" if k0 is None else k0)
            ok = (best==k0) if k0 is not None else (best is None)
            if not ok: allok=False
            print(f"  (a,b,c)≡({a},{b},{c}): identity holds with K0={best} (predicted {predicted}) {'OK' if ok else 'MISMATCH'}")
print("(V3) all cases as predicted:",allok)
print("(V4) lambda_M(psi-c)=0 exactly:", all(sum(phi_pow(a,b,M,c*M)[s]*(psiser(a,b,c*M)[c*M-s]-(c if s==c*M else 0)) for s in range(c*M+1))==0 for (a,b) in pairs[:5] for c in (1,2,3) for M in (1,2,3,6,9)))
