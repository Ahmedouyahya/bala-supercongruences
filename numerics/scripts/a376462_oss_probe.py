# Probe the intermediate congruences an OSS-type proof of A376462 would need.
# (W1) weighted block sums: v_p( sum'_{u<p^s} floor(u/p) / u^2 ) >= s ?
# (W2) the 'j-unscaled, i-scaled' class: Sigma := sum'_j sum_{i: p|i} (1/j^2) C(N-1,j-1)^2 C(N+j,j) C(N,i)^2 C(2N-j-i,N)  ==  0 mod p^r ?
#      and its level-1 reduction R1 := sum'_j (1/j^2) Psi(M,[j/p]), Psi(M,n') = C(M-1,n')^2 C(M+n',n') sum_{i'} C(M,i')^2 C(2M-i'-n'-1, M):  Sigma == R1 mod p^r ?
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
print("(W1) v_p(sum' floor(u/p)/u^2) - s:")
for p in (5,7,11):
    print("  p=%d:"%p, [(s, vp(sum(Fraction(u//p, u*u) for u in range(1,p**s) if u%p),p)-s) for s in (1,2,3)])
print("(W2) j-unscaled/i-scaled class and its level-1 reduction:")
for p in (5,7):
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            if N>250: continue
            Sig=sum(Fraction(C(N-1,j-1)**2*C(N+j,j)*C(N,i)**2*C(2*N-j-i,N), j*j) for j in range(1,N+1) if j%p for i in range(0,N+1,p))
            def Psi(n1): return C(M-1,n1)**2*C(M+n1,n1)*sum(C(M,i1)**2*C(2*M-i1-n1-1,M) for i1 in range(0,M+1))
            R1=sum(Fraction(Psi(j//p), j*j) for j in range(1,N+1) if j%p)
            print(f"  p={p} r={r} m={m}: v(Sigma)-r={vp(Sig,p)-r}, v(Sigma-R1)-r={vp(Sig-R1,p)-r}, v(R1)-r={vp(R1,p)-r}")
