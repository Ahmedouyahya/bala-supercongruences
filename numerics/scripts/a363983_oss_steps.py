# Step-by-step numerical verification of the OSS-style proof for A363983:
#   A(N,k) = (-1)^(N+k) C(N,k) C(N+k-1,k) C(2k,N),  a(N) = sum_k A(N,k).   N = m p^r, M = N/p.
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def A(N,k): return (-1)**(N+k)*comb(N,k)*comb(N+k-1,k)*comb(2*k,N) if k>=1 else (1 if N==0 else 0)
def D(n,k,j): return (-1)**k*comb(n-1,k)*comb(n+k,k)*comb(j,n)   # lower-level kernel
print("Step S (scaled terms): v_p(A(mp^r,kp^s) - A(mp^(r-1),kp^(s-1))) >= 3r for p∤k")
for p in (5,7):
    worst=99
    for r in (1,2):
        for m in (1,2):
            N=m*p**r; M=N//p
            for s in (1,2,3):
                for k in range(1, N//p**s+2):
                    if k%p==0: continue
                    d=A(N,k*p**s)-A(M,k*p**(s-1))
                    if d: worst=min(worst, vp(d,p)-3*r)
    print(f"  p={p}: min slack {worst}")
print("Step U1: unscaled sum G0(N) = sum_{p∤k} A(N,k): v_p >= 3r ;  and  G0(N) = (-1)^N N^2 * S  with S = sum'_k (-1)^k C(N-1,k-1)C(N+k-1,k-1)C(2k,N)/k^2")
for p in (5,7,11):
    for r in (1,2):
        for m in (1,2,3):
            N=m*p**r; M=N//p
            if N>600: continue
            G0=sum(A(N,k) for k in range(1,N+1) if k%p)
            S=sum(Fraction((-1)**k*comb(N-1,k-1)*comb(N+k-1,k-1)*comb(2*k,N), k*k) for k in range(1,N+1) if k%p)
            ok = (G0 == (-1)**N*N*N*S)
            # Step U2: S == - sum'_k D(M,[k/p],[2k/p])/k^2  (mod p^r)
            S1=sum(Fraction(D(M,k//p,2*k//p), k*k) for k in range(1,N+1) if k%p)
            # Step U3: Sigma_s := sum'_k D(m p^(r-s), [k/p^s],[2k/p^s])/k^2 ; Sigma_s == Sigma_{s+1} mod p^r, Sigma_r == 0 mod p^r
            sig=[sum(Fraction(D(m*p**(r-s), k//p**s, 2*k//p**s), k*k) for k in range(1,N+1) if k%p) for s in range(1,r+1)]
            chain=[vp(sig[i]-sig[i+1],p)-r for i in range(len(sig)-1)]
            print(f"  p={p} r={r} m={m}: v(G0)-3r={vp(G0,p)-3*r}, identity G0=(-1)^N N^2 S: {ok}, v(S + S1)-r = {vp(S+S1,p)-r}, Sigma chain slacks {chain}, v(Sigma_r)-r = {vp(sig[-1],p)-r}")
print("Lemma 2.2 (n=-2): sum'_{k<p^s} 1/k^2 == 0 mod p^s and half-sum sum'_{k<p^s/2} 1/k^2 == 0 mod p^s (p>=5):")
for p in (5,7,11,13):
    print("  p=%d:"%p, [(s, vp(sum(Fraction(1,k*k) for k in range(1,p**s) if k%p),p)-s, vp(sum(Fraction(1,k*k) for k in range(1,(p**s+1)//2) if k%p),p)-s) for s in (1,2,3)])
print("Lemma 2.4-type reductions mod p^r (random spot checks):")
import random
random.seed(3); bad=0; tot=0
for _ in range(400):
    p=random.choice((5,7,11)); r=random.choice((1,2,3)); m=random.randint(1,3); N=m*p**r; M=N//p
    k=random.randint(1,N)
    if k%p==0: continue
    tot+=1
    c1=((-1)**(k-1)*comb(N-1,k-1) - (-1)**(k//p)*comb(M-1,k//p))%p**r
    c2=(comb(N+k-1,k-1) - comb(M+k//p,k//p))%p**r
    c3=(comb(2*k,N) - comb(2*k//p,M))%p**r
    if c1 or c2 or c3: bad+=1
print(f"  {tot} checks, failures: {bad}")
