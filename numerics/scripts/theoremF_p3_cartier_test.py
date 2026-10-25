# p=3, r=1.  Condition:  [y^{cm}] phi(y)^m ( Q(y) + m L(y) ) ≡ 0 (mod 3),  Q := Cartier_3(L^2) (3-section), everything over F_3.
# Hypothesis ("total derivative" mechanism): Q ≡ D g  and  L ≡ g (psi - c)  (mod 3) with g = L/(psi - c), psi = x phi'/phi = x(alpha + beta x)/(1-x^2),
# because [y^{cm}] phi^m (D g + m g (psi - c)) = [y^{cm}] y^{cm} D( phi^m y^{-cm} g ) = 0 exactly.
# Test  Q ≡ D(L/(psi-c)) (mod 3)  coefficientwise to high order, for all (a,b) mod 3 and c in {1,2}.
P=3; K=90
def inv_series(f):  # f[0] unit mod P
    g=[0]*(K+1); g[0]=pow(f[0],-1,P)
    for n in range(1,K+1):
        s=sum(f[i]*g[n-i] for i in range(1,n+1) if i<len(f))%P
        g[n]=(-s*g[0])%P
    return g
def mul(f,g):
    h=[0]*(K+1)
    for i,x in enumerate(f):
        if x==0: continue
        for j,y in enumerate(g):
            if i+j>K: break
            h[i+j]=(h[i+j]+x*y)%P
    return h
def D(f): return [(i*f[i])%P for i in range(K+1)]
def cartier(f): return [f[P*t]%P if P*t<=K else 0 for t in range(K+1)]
def series_L(a,b):
    f=[0]*(K+1)
    for i in range(1,K+1):
        if i%P: f[i]=((a*(-1)**(i+1)-b)*pow(i,-1,P))%P
    return f
def series_psi(a,b):
    # psi = a x/(1+x) - b x/(1-x) = sum_i (a(-1)^{i+1} - b) x^i  (i>=1)
    return [0]+[((a*(-1)**(i+1)-b))%P for i in range(1,K+1)]
res={}
for c in (1,2):
    for a in range(3):
        for b in range(3):
            L=series_L(a,b); psi=series_psi(a,b)
            den=[((psi[i])-(c if i==0 else 0))%P for i in range(K+1)]
            g=mul(L,inv_series(den))
            Q=cartier(mul(L,L))
            Dg=D(g)
            diff=[(Q[t]-Dg[t])%P for t in range(K//P)]
            ok=all(d==0 for d in diff)
            # also check the weaker property: is [y^{cm}] phi^m (Q - Dg) ≡ 0 for m=1..12?  (phi^m via binomials mod 3)
            res[(a,b,c)]=(ok, diff[:12])
            print(f"(a,b,c)≡({a},{b},{c}): Q ≡ D(L/(psi-c))? {ok}   first coeffs of Q-Dg: {diff[:10]}")
