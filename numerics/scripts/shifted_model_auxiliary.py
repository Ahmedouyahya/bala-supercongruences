# Model problem A'(n)=sum C(n,k)^2 C(n+k,k): the class-K analysis at level N=pM reduces (via the hypergeometric relation
# (2-M) mu_2 = (M^2-1) mu_1 - M(M-1)^2 mu_0 for mu_t = sum k^t C(M-1,k)^2 C(M+k-1,k)) to
#   V(M) := sum_k C(M-1,k)^2 C(M+k,k) ≡ 0 (mod p^s),  s = v_p(M).
# Check: (a) the hypergeometric relation exactly; (b) Q1 = [3 mu_1 - M(2M-3) mu_0]/(2-M) exactly; (c) V(M) mod p^s;
# (d) V(M) = (1/M^2)[M^2 A'(M) - 2M m1' + m2'] with m_t' = sum k^t C(M,k)^2 C(M+k,k): valuations of the three pieces;
# (e) the A376462 analogue: V2(M) := sum_{k,j} C(M-1,k)^2 C(M+k,k) C(M-1,k+j)^2 C(M+j-1,j)  mod p^s ?  and symmetric variants.
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
ok_rel=True; ok_Q=True
for M in range(1,40):
    mu=[sum(k**t*C(M-1,k)**2*C(M+k-1,k) for k in range(M)) for t in range(3)]
    if (2-M)*mu[2]!=(M*M-1)*mu[1]-M*(M-1)**2*mu[0]: ok_rel=False
    Q1=sum((2*k+1)*C(M-1,k)**2*C(M+k,k) for k in range(M))
    if M!=2 and Fraction(3*mu[1]-M*(2*M-3)*mu[0],2-M)!=Q1: ok_Q=False
print("(a) hypergeometric moment relation exact for M<40:",ok_rel,"  (b) Q1 formula exact:",ok_Q)
for p in (5,7,11,13):
    for s in (1,2,3):
        for m in (1,2,3):
            M=m*p**s
            if M>400: continue
            V=sum(C(M-1,k)**2*C(M+k,k) for k in range(M))
            Ap=sum(C(M,k)**2*C(M+k,k) for k in range(M+1))
            m1=sum(k*C(M,k)**2*C(M+k,k) for k in range(M+1)); m2=sum(k*k*C(M,k)**2*C(M+k,k) for k in range(M+1))
            extra=''
            if M<=80:
                V2=sum(C(M-1,k)**2*C(M+k,k)*C(M-1,k+j)**2*C(M+j-1,j) for k in range(M) for j in range(M-k))
                extra=f" | A376462 analogue V2: v-s={vp(V2,p)-s}"
            print(f"p={p} M={M} s={s}: v(V)-s={vp(V,p)-s}; pieces v(M^2A')={vp(M*M*Ap,p)} v(2M m1')={vp(2*M*m1,p)} v(m2')={vp(m2,p)} v(sum)-3s={vp(M*M*Ap-2*M*m1+m2,p)-3*s}{extra}")
