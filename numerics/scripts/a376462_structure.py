# A376462: a(n) = sum_{k,i} C(n,k)^2 C(n+k,k) C(n,i)^2 C(2n-k-i, n).  Explore structure for an OSS-type proof.
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def T(n,k,i): return comb(n,k)**2*comb(n+k,k)*comb(n,i)**2*comb(2*n-k-i,n) if 2*n-k-i>=n else 0
def a(n): return sum(T(n,k,i) for k in range(n+1) for i in range(n+1))
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a_def(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
print("double-sum form agrees with OEIS definition n<=12:", all(a(n)==a_def(n) for n in range(13)))
# inner sum over k: I(n,i) = sum_k C(n,k)^2 C(n+k,k) C(2n-i-k, n); and over i: J(n,k) = sum_i C(n,i)^2 C(2n-k-i,n) = A108625(n,n-k)
print("values:", [a(n) for n in range(7)])
# classification of terms by divisibility of k and i by p, for N = m p^r
for p in (5,7):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            if N>300: continue
            tot=a(N)-a(M)
            both=sum(T(N,p*k,p*i)-T(M,k,i) for k in range(M+1) for i in range(M+1))
            rest=sum(T(N,k,i) for k in range(N+1) for i in range(N+1) if k%p or i%p)
            # finer: k unscaled only, i unscaled only, both unscaled
            ku=sum(T(N,k,i) for k in range(N+1) for i in range(N+1) if k%p and i%p==0)
            iu=sum(T(N,k,i) for k in range(N+1) for i in range(N+1) if k%p==0 and i%p)
            bu=sum(T(N,k,i) for k in range(N+1) for i in range(N+1) if k%p and i%p)
            tw=min((vp(T(N,p*k,p*i)-T(M,k,i),p) for k in range(M+1) for i in range(M+1) if T(N,p*k,p*i)-T(M,k,i)), default=999)
            print(f"p={p} r={r} m={m}: v(a(N)-a(M))-3r={vp(tot,p)-3*r}; scaled-diff sum {vp(both,p)-3*r}, termwise min {tw-3*r}; unscaled: k-only {vp(ku,p)-3*r}, i-only {vp(iu,p)-3*r}, both {vp(bu,p)-3*r}")
# second conjecture a(np^r - 1) == a(np^(r-1) - 1)
print("second congruence check:", [(p,r,m, vp(a(m*p**r-1)-a(m*p**(r-1)-1),p)-3*r) for p in (5,7) for r in (1,2) for m in (1,2) if m*p**r<=300])
