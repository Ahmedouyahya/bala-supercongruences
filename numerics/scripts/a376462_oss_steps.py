# Step-by-step verification of the OSS-type proof of A376462's FIRST congruence a(mp^r) == a(mp^(r-1)) mod p^(3r).
# T(N;k,i) = C(N,k)^2 C(N+k,k) C(N,i)^2 C(2N-k-i,N).  Classes: (S) p|k,p|i ; (K) p∤k,p|i ; (I) p|k,p∤i ; (B) p∤k,p∤i.
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
def T(N,k,i): return C(N,k)**2*C(N+k,k)*C(N,i)**2*C(2*N-k-i,N)
def Psi1(M,n1): return C(M-1,n1)**2*C(M+n1,n1)*sum(C(M,i1)**2*C(2*M-n1-1-i1,M) for i1 in range(0,M+1))
def Psi2(M,n1): return C(M-1,n1)**2*sum(C(M,k1)**2*C(M+k1,k1)*C(2*M-k1-n1-1,M) for k1 in range(0,M+1))
print("self-similarity: Psi_j(m p^t, n') == Psi_j(m p^(t-1), [n'/p]) mod p^t ?")
for p in (5,7):
    bad1=bad2=0; tot=0
    for t in (1,2):
        for m in (1,2):
            Mt=m*p**t
            for n1 in range(0,2*Mt+2):
                tot+=1
                if (Psi1(Mt,n1)-Psi1(Mt//p,n1//p))%p**t: bad1+=1
                if (Psi2(Mt,n1)-Psi2(Mt//p,n1//p))%p**t: bad2+=1
    print(f"  p={p}: {tot} checks, failures Psi1: {bad1}, Psi2: {bad2}")
print("classes and chains (slack vs required):")
for p in (5,7):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            if N>250: continue
            S=sum(T(N,p*k,p*i)-T(M,k,i) for k in range(M+1) for i in range(M+1))
            tw=min((vp(T(N,p*k,p*i)-T(M,k,i),p) for k in range(M+1) for i in range(M+1) if T(N,p*k,p*i)-T(M,k,i)),default=999)
            K=sum(T(N,k,i) for k in range(1,N+1) if k%p for i in range(0,N+1,p))
            I=sum(T(N,k,i) for k in range(0,N+1,p) for i in range(1,N+1) if i%p)
            B=sum(T(N,k,i) for k in range(1,N+1) if k%p for i in range(1,N+1) if i%p)
            # reductions: K == N^2 * SigK1, SigK_s := sum'_k Psi1(m p^(r-s),[k/p^s])/k^2 ; same for I with Psi2
            SK=[sum(Fraction(Psi1(m*p**(r-s),k//p**s),k*k) for k in range(1,N+1) if k%p) for s in range(1,r+1)]
            SI=[sum(Fraction(Psi2(m*p**(r-s),i//p**s),i*i) for i in range(1,N+1) if i%p) for s in range(1,r+1)]
            Kexact=sum(Fraction(C(N-1,k-1)**2*C(N+k,k)*C(N,i)**2*C(2*N-k-i,N),k*k) for k in range(1,N+1) if k%p for i in range(0,N+1,p))
            Iexact=sum(Fraction(C(N-1,i-1)**2*C(N,k)**2*C(N+k,k)*C(2*N-k-i,N),i*i) for k in range(0,N+1,p) for i in range(1,N+1) if i%p)
            print(f"  p={p} r={r} m={m}: scaled sum {vp(S,p)-3*r} (termwise {tw-3*r}); K {vp(K,p)-3*r}, I {vp(I,p)-3*r}, B {vp(B,p)-3*r} | K=N^2*Kexact {K==N*N*Kexact}, v(Kexact-SigK1)-r={vp(Kexact-SK[0],p)-r}, chainK={[vp(SK[j]-SK[j+1],p)-r for j in range(r-1)]}, v(SigK_r)-r={vp(SK[-1],p)-r} | I=N^2*Iexact {I==N*N*Iexact}, v(Iexact-SigI1)-r={vp(Iexact-SI[0],p)-r}, chainI={[vp(SI[j]-SI[j+1],p)-r for j in range(r-1)]}, v(SigI_r)-r={vp(SI[-1],p)-r}")
