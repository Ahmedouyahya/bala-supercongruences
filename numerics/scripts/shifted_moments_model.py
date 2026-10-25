# Model problem: A'(n) = sum_k C(n,k)^2 C(n+k,k) (Apéry zeta(2) numbers), shifted congruence A'(mp^r-1) ≡ A'(mp^{r-1}-1) (mod p^{3r}) [Beukers 1985].
# The second-order analysis of the A=1 class predicts the need for moment congruences at level M (s = v_p(M)):
#   Q1(M) := sum_{n'} (2n'+1) C(M-1,n')^2 C(M+n',n')  ≡ 0 (mod p^{2s}) ?
# and for A376462 with Psi(M,n') = C(M-1,n')^2 C(M+n',n') T(M,n'),  T(M,n') = sum_j C(M-1,n'+j)^2 C(M+j-1,j):
#   Q2(M) := sum_{n'} (2n'+1) Psi(M,n')  ≡ 0 (mod p^{2s}) ?
# Also: the class sums of the model problem at r=1,2 (do they vanish individually?), and general moments mu_t = sum n'^t S'_M(n').
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def Ap(n): return sum(C(n,k)**2*C(n+k,k) for k in range(n+1))
def T(M,n1): return sum(C(M-1,n1+j)**2*C(M+j-1,j) for j in range(0,M))
print("model shifted congruence slack:", [(p,r,m,vp(Ap(m*p**r-1)-Ap(m*p**(r-1)-1),p)-3*r) for p in (5,7) for r in (1,2) for m in (1,2)])
for p in (5,7,11):
    for s in (0,1,2):
        for m in (1,2):
            M=m*p**s
            if M>130: continue
            Q1=sum((2*n1+1)*C(M-1,n1)**2*C(M+n1,n1) for n1 in range(M))
            Q2=sum((2*n1+1)*C(M-1,n1)**2*C(M+n1,n1)*T(M,n1) for n1 in range(M)) if M<=60 else None
            mus=[sum(n1**t*C(M-1,n1)**2*C(M+n1-1,n1) for n1 in range(M)) for t in range(4)]
            print(f"p={p} M={M} (s={s}): v(Q1)-2s={vp(Q1,p)-2*s}  v(Q2)-2s={vp(Q2,p)-2*s if Q2 is not None else '-'}   moments mu_t of model shifted terms: v={[vp(x,p) for x in mus]}")
# class sums of the model problem
print("model problem class sums (scaled k | unscaled k) slack vs p^{3r}:")
for p in (5,7):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=m*p**(r-1)
            sc=sum(C(N-1,k)**2*C(N+k-1,k) for k in range(0,N,p)); un=sum(C(N-1,k)**2*C(N+k-1,k) for k in range(N) if k%p)
            print(f"  p={p} r={r} m={m}: scaled-A'(M-1): {vp(sc-Ap(M-1),p)-3*r:+d}, unscaled: {vp(un,p)-3*r:+d}")
