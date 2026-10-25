# Dissect the shifted congruence at r=2 (N = m p^2, M = m p): which sub-congruences would a second-order proof need?
# Class K: Sigma_K = N * sum'_k B(k)/k.  Expand B(k) = Psi(M,[k/p]) * (1 - N*(3H'_k + 1/k)) + O(N^2) exactly? test mod p^4.
# Then T0 := sum'_k Psi(M,[k/p])/k  and  T1 := sum'_k Psi(M,[k/p]) (3H'_k + 1/k)/k ; need T0 - N*T1 == 0 mod p^4 (so Sigma_K == 0 mod p^6).
# Check: v_p(T0) >= 4 ?  v_p(T1) >= 2 ?  And decompose T0 = sum_{n'} Psi(M,n') sigma(n'),  sigma(n') = sum'_{[k/p]=n'} 1/k (== 0 mod p^2).
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
def Hp(k,p): return sum(Fraction(1,i) for i in range(1,k+1) if i%p)
def Psi(M,n1): return C(M-1,n1)**2*C(M+n1,n1)*sum(C(M-1,n1+j1)**2*C(M+j1-1,j1) for j1 in range(0,M))
def B(N,k): return C(N-1,k)**2*C(N+k-1,k-1)*sum(C(N-1,k+p*j1)**2*C(N+p*j1-1,p*j1) for j1 in range(0,N//p))
for p in (5,7):
    for m in (1,2):
        r=2; N=m*p**r; M=N//p
        # exactness of first-order model mod p^4
        bad=0
        for k in range(1,N):
            if k%p: 
                model=Psi(M,k//p)*(1-N*(3*Hp(k,p)+Fraction(1,k)))
                if vp(B(N,k)-model,p)<4: bad+=1
        T0=sum(Fraction(Psi(M,k//p),k) for k in range(1,N) if k%p)
        T1=sum(Psi(M,k//p)*(3*Hp(k,p)+Fraction(1,k))/k for k in range(1,N) if k%p)
        SK=sum(Fraction(B(N,k),k) for k in range(1,N) if k%p)
        # block decomposition of T0 by level-2 blocks n'' = [k/p^2]
        sig=lambda n1: sum(Fraction(1,n1*p+u) for u in range(1,p))
        T0_blocks=[sum(Psi(M,n1)*sig(n1) for n1 in range(n2*p,(n2+1)*p)) for n2 in range(0,m)]
        # Psi self-similarity with first-order correction: Psi(M,n') vs Psi(m,[n'/p]) mod p^2 and the ratio structure
        ratio_dev=[vp(Psi(M,n1)-Psi(m,n1//p),p) for n1 in range(0,M) if Psi(m,n1//p)]
        print(f"p={p} m={m} (r=2): first-order model failures mod p^4: {bad}; v(S_K)-4={vp(SK,p)-4}; v(T0)-4={vp(T0,p)-4}; v(T1)-2={vp(T1,p)-2}; T0 block valuations-4: {[vp(x,p)-4 for x in T0_blocks]}; min v(Psi(M,n')-Psi(m,[n'/p])) = {min(ratio_dev)} (expect 1)")
