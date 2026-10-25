# (1) c ≡ 0 mod 3 (A333562 has c=3): r=1 test of Q ≡ D(L/psi) over F_3 (Laurent division), vs. the c=3 sweep.
# (2) r>=2: solve (D + M(psi-c)) g = h,  h = C(L^2) + M*L  (exact rationals), check 3-integrality of g_t (t<cM), compare g mod 3 with L/(psi-c), and the final constraint.
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
def modp(x):
    x=Fraction(x); assert x.denominator%P
    return (x.numerator*pow(x.denominator,-1,P))%P
# ---------- part 1: c ≡ 0 ----------
K=90
def mulF(f,g):
    h=[0]*(K+1)
    for i,x in enumerate(f):
        if x==0: continue
        for j,y in enumerate(g):
            if i+j>K: break
            h[i+j]=(h[i+j]+x*y)%P
    return h
def invF(f):
    g=[0]*(K+1); g[0]=pow(f[0],-1,P)
    for n in range(1,K+1):
        s=sum(f[i]*g[n-i] for i in range(1,n+1))%P
        g[n]=(-s*g[0])%P
    return g
print("=== c ≡ 0 (mod 3), r=1: is C(L^2) ≡ D(L/psi) ? ===")
for a in range(3):
    for b in range(3):
        if (a,b)==(0,0): continue
        L=[0]+[((a*(-1)**(i+1)-b)*pow(i,-1,P))%P if i%P else 0 for i in range(1,K+1)]
        psi=[0]+[((a*(-1)**(i+1)-b))%P for i in range(1,K+1)]
        # Laurent division: psi = x^k u with u(0)!=0
        k=next(i for i in range(K+1) if psi[i])
        u=psi[k:]+[0]*k
        Lk=L[k:]+[0]*k   # L / x^k (L has order >= k? check)
        assert all(L[i]==0 for i in range(k)), (a,b,L[:k])
        g=mulF(Lk,invF(u))
        Dg=[(i*g[i])%P for i in range(K+1)]
        Q=[mulF(L,L)[P*t] if P*t<=K else 0 for t in range(K+1)]
        ok=all(Q[t]==Dg[t] for t in range(K//P))
        print(f"  (a,b)≡({a},{b}): {ok}   diff: {[(Q[t]-Dg[t])%P for t in range(10)]}")
# ---------- part 2: lift to r>=2 ----------
print("=== r>=2: solve (D + M(psi-c)) g = h exactly, h = C(L^2) + M L ===")
def L_exact(a,b,K):
    return [Fraction(0)]+[Fraction(a*(-1)**(i+1)-b,i) if i%P else Fraction(0) for i in range(1,K+1)]
def mulQ(f,g,K):
    h=[Fraction(0)]*(K+1)
    for i,x in enumerate(f):
        if x==0: continue
        for j,y in enumerate(g):
            if i+j>K: break
            h[i+j]+=x*y
    return h
for (a,b,c) in ((2,-1,1),(3,-1,2),(-1,2,1),(5,2,1),(1,1,2)):
    for r in (2,3):
        for m in (1,2):
            M=m*P**(r-1); KK=P*c*M
            L=L_exact(a,b,KK); L2=mulQ(L,L,KK)
            h=[L2[P*t]+ (M*L[t] if t<=KK else 0) for t in range(c*M+1)]
            ell=[0]+[a*(-1)**(i+1)-b for i in range(1,c*M+1)]
            g=[Fraction(0)]*(c*M+1)
            for t in range(1,c*M):
                s=h[t]-M*sum(ell[i]*g[t-i] for i in range(1,t+1))
                g[t]=s/(t-c*M)
            constraint=h[c*M]-M*sum(ell[i]*g[c*M-i] for i in range(1,c*M+1))
            minv=min(vp(g[t]) for t in range(1,c*M))
            # compare g mod 3 with L/(psi-c) mod 3 (first coefficients)
            print(f"  (a,b,c)=({a},{b},{c}) r={r} m={m}: min v3(g_t)={minv}; v3(constraint)-r={vp(constraint)-r}  [need >=0]; v3(constraint) raw={vp(constraint)}")
