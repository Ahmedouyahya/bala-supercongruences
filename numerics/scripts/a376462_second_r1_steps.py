# Sub-claims for a(mp-1) == a(m-1) mod p^3 (r=1), p>=5, in the representation S~(N;k,j)=C(N-1,k)^2 C(N+k-1,k) C(N-1,k+j)^2 C(N+j-1,j).
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def St(N,k,j): return C(N-1,k)**2*C(N+k-1,k)*C(N-1,k+j)**2*C(N+j-1,j)
def Hp(k,p): return sum(Fraction(1,i) for i in range(1,k+1) if i%p)   # H'_k
print("(i) double harmonic sums mod p: sum_{u+v<p} 1/(uv), sum_{u+v>=p, u,v<p} 1/(uv), sum_{u<p} H_u/u:")
for p in (5,7,11,13):
    s1=sum(Fraction(1,u*v) for u in range(1,p) for v in range(1,p) if u+v<p); s2=sum(Fraction(1,u*v) for u in range(1,p) for v in range(1,p) if u+v>=p)
    s3=sum(Hp(u,p)/u for u in range(1,p))
    print(f"  p={p}: v_p = {vp(s1,p)}, {vp(s2,p)}, {vp(s3,p)}")
print("(ii) first-order expansions mod p^2 (N=mp, p∤k, n'=[k/p]):")
for p in (5,7,11):
    for m in (1,2,3):
        N=m*p; bad=[0,0,0,0]
        for k in range(1,N):
            if k%p==0: continue
            n1=k//p; H=Hp(k,p)
            # (a) C(N-1,k)^2 == C(m-1,n')^2 (1 - 2 p m H'_k)
            if vp(C(N-1,k)**2 - C(m-1,n1)**2*(1-2*p*m*H),p) < 2: bad[0]+=1
            # (b) C(N+k-1,k-1) == C(m+n',n') (1 + p m (H'_k - 1/k))
            if vp(C(N+k-1,k-1) - C(m+n1,n1)*(1+p*m*(H-Fraction(1,k))),p) < 2: bad[1]+=1
            # (c) for all j': C(N-1,k+pj')^2 == C(m-1,n'+j')^2 (1 - 2 p m H'_k) and C(N+pj'-1,pj') == C(m+j'-1,j') mod p^2
            for j1 in range(0,m):
                if vp(C(N-1,k+p*j1)**2 - C(m-1,n1+j1)**2*(1-2*p*m*H),p) < 2: bad[2]+=1
                if vp(C(N+p*j1-1,p*j1) - C(m+j1-1,j1),p) < 2: bad[3]+=1
        print(f"  p={p} m={m}: failures (a),(b),(c1),(c2) = {bad}")
print("(iii) block sums mod p^2 / p: sum'_{block} 1/k (mod p^2), sum'_{block} 1/k^2 (mod p), sum'_{block} H'_k/k (mod p):")
for p in (5,7,11):
    for n1 in range(0,4):
        b1=sum(Fraction(1,n1*p+u) for u in range(1,p)); b2=sum(Fraction(1,(n1*p+u)**2) for u in range(1,p)); b3=sum(Hp(n1*p+u,p)/(n1*p+u) for u in range(1,p))
        print(f"  p={p} block {n1}: v({'1/k'})-2={vp(b1,p)-2}, v(1/k^2)-1={vp(b2,p)-1}, v(H'/k)-1={vp(b3,p)-1}")
print("(iv) assembled classes at r=1 (slack vs p^3): KU, JU, BU, scaled termwise:")
for p in (5,7,11,13):
    for m in (1,2,3,4):
        N=m*p
        KU=sum(St(N,k,j) for k in range(N) if k%p for j in range(0,N-k,p)); JU=sum(St(N,k,j) for k in range(0,N,p) for j in range(N-k) if j%p); BU=sum(St(N,k,j) for k in range(N) if k%p for j in range(N-k) if j%p)
        tw=min((vp(St(N,p*k,p*j)-St(m,k,j),p) for k in range(m) for j in range(m-k) if St(N,p*k,p*j)-St(m,k,j)),default=999)
        print(f"  p={p} m={m}: KU {vp(KU,p)-3}, JU {vp(JU,p)-3}, BU {vp(BU,p)-3}, scaled termwise {tw-3 if tw<999 else 'n/a'}, total {vp(sum(St(N,k,j) for k in range(N) for j in range(N-k))-sum(St(m,k,j) for k in range(m) for j in range(m-k)),p)-3}")
