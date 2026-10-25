# Second congruence of A376462 via the representation  a(N-1) = sum_{k,j} S~(N;k,j),
#   S~(N;k,j) = C(N-1,k)^2 C(N+k-1,k) C(N-1,k+j)^2 C(N+j-1,j)      (k,j>=0, k+j<=N-1).
# Classes by divisibility of k and j. Test which classes vanish mod p^(3r), and the '1/k-weight' reduction for the singly-unscaled classes.
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
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
print("representation check a(N-1) = sum S~:", all(a(N-1)==sum(St(N,k,j) for k in range(N) for j in range(N-k)) for N in range(1,14)))
for p in (5,7,11):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            if N>260: continue
            tot=a(N-1)-a(M-1)
            SS=sum(St(N,p*k,p*j) for k in range(M) for j in range(M-k))        # both scaled (k,j multiples of p)
            SSl=sum(St(M,k,j) for k in range(M) for j in range(M-k))            # lower level
            KU=sum(St(N,k,j) for k in range(N) if k%p for j in range(0,N-k,p))  # k unscaled, j scaled
            JU=sum(St(N,k,j) for k in range(0,N,p) for j in range(N-k) if j%p)  # k scaled, j unscaled
            BU=sum(St(N,k,j) for k in range(N) if k%p for j in range(N-k) if j%p)
            tw=min((vp(St(N,p*k,p*j)-St(M,k,j),p) for k in range(M) for j in range(M-k) if St(N,p*k,p*j)-St(M,k,j)),default=999)
            print(f"p={p} r={r} m={m}: total {vp(tot,p)-3*r} | scaled-diff sum {vp(SS-SSl,p)-3*r} (termwise {tw-3*r}) | KU {vp(KU,p)-3*r}, JU {vp(JU,p)-3*r}, BU {vp(BU,p)-3*r} | min termwise v: KU {min(vp(St(N,k,j),p) for k in range(N) if k%p for j in range(0,N-k,p))}, BU {min(vp(St(N,k,j),p) for k in range(N) if k%p for j in range(N-k) if j%p)}")
