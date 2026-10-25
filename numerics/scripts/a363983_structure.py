# A363983: a(n) = sum_{k} (-1)^(n+k) C(n,k) C(n+k-1,k) C(2k,n). Explore the OSS-style decomposition at N = n p^r:
#   scaled terms (p | k) vs unscaled terms (p ∤ k): valuations of the unscaled sum and of the scaled-difference sum.
from math import comb
def vp(x,p):
    if x==0: return 999
    v=0
    while x%p==0: x//=p; v+=1
    return v
def A(N,k): return (-1)**(N+k)*comb(N,k)*comb(N+k-1,k)*comb(2*k,N) if N>0 else (1 if k==0 else 0)
def a(N): return sum(A(N,k) for k in range(0,N+1))
print("check:", [a(N) for N in range(8)])
print(" p n r | v(a(N)-a(M)) | v(unscaled sum) | v(scaled diff sum) | min termwise v(A(N,pk)-A(M,k)) | min v(unscaled term)")
for p in (5,7,11,13):
    for n in (1,2,3):
        for r in (1,2):
            N=n*p**r; M=N//p
            if N>700: continue
            uns=sum(A(N,k) for k in range(0,N+1) if k%p)
            sc=sum(A(N,p*k)-A(M,k) for k in range(0,M+1))
            tw=min((vp(A(N,p*k)-A(M,k),p) for k in range(0,M+1)), default=999)
            tu=min((vp(A(N,k),p) for k in range(0,N+1) if k%p and A(N,k)), default=999)
            print(f"{p:2d} {n} {r} | {vp(a(N)-a(M),p):3d} | {vp(uns,p):3d} | {vp(sc,p):3d} | {tw:3d} | {tu:3d}   (3r={3*r})")
