# Numerics sweep for the remaining Tier-A items (exact integer arithmetic). Run: python -I numerics/sweep_2026-10-15.py
from math import comb, factorial
from fractions import Fraction
import sys
def vp(x,p):
    if x==0: return 'inf'
    v=0
    while x%p==0: x//=p; v+=1
    return v
# ---------- beta(S,N) = [X^N] G(X) (1-X)^{-S}, G=(1-2X)/((1-X)(1-X+X^2)) ----------
def series_inv_1mXpX2(n):  # coefficients of 1/(1-X+X^2) : periodic 1,1,0,-1,-1,0
    pat=[1,1,0,-1,-1,0]; return [pat[i%6] for i in range(n+1)]
def beta(S,N):
    # G = (1-2X) * 1/(1-X) * 1/(1-X+X^2); then times (1-X)^{-S} => (1-2X) * (1-X)^{-(S+1)} / (1-X+X^2)
    inv=series_inv_1mXpX2(N)
    # (1-2X)*inv
    g=[inv[i]-(2*inv[i-1] if i>=1 else 0) for i in range(N+1)]
    # (1-X)^{-(S+1)} coefficients: C(S+i, i)
    tot=0
    for i in range(N+1):
        tot+=g[i]*comb(S+N-i, N-i)
    return tot
def T(r,N):  # sum_{k<=N} [x^k] c(x)^r, c = Catalan gf; [x^k]c^r = r/(r+2k) C(r+2k,k)
    return sum(Fraction(r, r+2*k)*comb(r+2*k,k) for k in range(N+1)) if r>0 else None
print("== identity T(r,N) = beta(r+N, N) (Catalan truncation = Epoch beta) ==")
bad=0
for r in range(1,9):
    for N in range(0,9):
        if T(r,N)!=beta(r+N,N): bad+=1; print("  MISMATCH",r,N,T(r,N),beta(r+N,N))
print("  mismatches:",bad)
print("== two-parameter shift: v_p(beta(pS,pN)-beta(S,N)) for independent S,N (need >= 3(v+1), v=min v_p(S),v_p(N)) ==")
for p in (5,7,11,13):
    worst=None
    for S in range(1,40):
        for N in range(1,25):
            v=min(vp(S,p) if S else 99, vp(N,p) if N else 99)
            if not isinstance(v,int): continue
            d=beta(p*S,p*N)-beta(S,N)
            val=vp(d,p)
            if val=='inf': continue
            slack=val-3*(v+1)
            if worst is None or slack<worst[0]: worst=(slack,S,N,val,v)
    print(f"  p={p}: minimal slack {worst[0]} at S={worst[1]},N={worst[2]} (v={worst[4]}, val={worst[3]})")
print("== A352275 / u_m(n): v_p(u_m(np^k)-u_m(np^(k-1))) ==")
def u(m,n): return 1 if n==0 else sum(Fraction(n,n+2*k)*comb(n+2*k,k) for k in range(m*n+1))
for m in (1,2,3):
    for p in (5,7,11):
        row=[]
        for k in (1,2):
            for n in (1,2):
                if n*p**k>250: continue
                row.append(f"n={n},k={k}:{vp(u(m,n*p**k)-u(m,n*p**(k-1)),p)}")
        print(f"  m={m} p={p}: "+" ".join(row))
# ---------- A386548 ----------
def A386548(n): return sum((-1)**k*comb(n+k-1,k)*comb(n-k-1,n-2*k) for k in range(n//2+1)) if n>0 else 1
print("== A386548: v_p(a(np^k)-a(np^(k-1))), conjecture >= 2k ==")
for p in (5,7,11,13):
    row=[]
    for k in (1,2):
        for n in (1,2,3):
            if n*p**k>400: continue
            row.append(f"n={n},k={k}:{vp(A386548(n*p**k)-A386548(n*p**(k-1)),p)}")
    print(f"  p={p}: "+" ".join(row))
print("   p=3 check:", [ (n,k,vp(A386548(n*3**k)-A386548(n*3**(k-1)),3)) for k in (1,2,3) for n in (1,2)])
# ---------- A361711 ----------
def A361711(n):
    if n==1: return 1
    return sum((-1)**k*comb(n,k)**2*comb(n-2,k) for k in range(0,n-1))
def A361711_odd(M):  # closed form for odd M=2n+1: (-1)^n (3n+1)/(2n+1) (3n)!/n!^3
    n=(M-1)//2
    return (-1)**n*Fraction(3*n+1,2*n+1)*Fraction(factorial(3*n),factorial(n)**3)
print("== A361711 closed form check and valuations, need >= 3k ==")
print("   closed form ok:", all(A361711(M)==A361711_odd(M) for M in range(3,40,2)))
for p in (5,7,11,13,17,19,23):
    row=[]
    for k in (1,2,3):
        if p**k>5000: continue
        d=A361711_odd(p**k)-A361711_odd(p**(k-1)) if k>1 else A361711_odd(p)-1
        row.append(f"k={k}:{vp(int(d),p)}")
    print(f"  p={p}: "+" ".join(row))
# ---------- A364178, A364175 ----------
from math import gcd
def gamma_fact_ratio_A364178(n):
    # (10n)!(3n)!(n/2)!/((6n)!(5n)!(3n/2)! n!) ; for odd n use Gamma at half-integers: (m/2)! = Gamma(m/2+1)
    # ratio (n/2)!/(3n/2)! = 1/prod_{j=1}^{n} (n/2+j)  -> exact rational
    den=Fraction(1)
    for j in range(1,n+1): den*=Fraction(n,2)+j
    return Fraction(factorial(10*n)*factorial(3*n), factorial(6*n)*factorial(5*n)*factorial(n))/den
def A364175(n):
    # (6n)!(2n/3)!/((3n)!(2n)!(5n/3)!) = (6n)!/((3n)!(2n)!) / prod_{j=1}^{n} (2n/3 + j)
    den=Fraction(1)
    for j in range(1,n+1): den*=Fraction(2*n,3)+j
    return Fraction(factorial(6*n), factorial(3*n)*factorial(2*n))/den
print("== A364178 first terms:", [gamma_fact_ratio_A364178(n) for n in range(0,5)])
print("== A364175 first terms:", [A364175(n) for n in range(0,5)])
for name,f in (("A364178",gamma_fact_ratio_A364178),("A364175",A364175)):
    for p in (5,7,11,13):
        row=[]
        for k in (1,2):
            for n in (1,2):
                if n*p**k>200: continue
                d=f(n*p**k)-f(n*p**(k-1))
                assert d.denominator==1, (name,n,p,k,d.denominator)
                row.append(f"n={n},k={k}:{vp(int(d),p)}")
        print(f"  {name} p={p}: "+" ".join(row))
# ---------- A363983, A376462 ----------
def A363983(n): return sum((-1)**(n+k)*comb(n,k)*comb(n+k-1,k)*comb(2*k,n) for k in range((n+1)//2, n+1)) if n>0 else 1
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def A376462(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
print("== A363983 check:", [A363983(n) for n in range(8)])
for p in (5,7,11,13):
    row=[]
    for k in (1,2):
        for n in (1,2,3):
            if n*p**k>400: continue
            row.append(f"n={n},k={k}:{vp(A363983(n*p**k)-A363983(n*p**(k-1)),p)}")
    print(f"  A363983 p={p}: "+" ".join(row))
print("== A376462 check:", [A376462(n) for n in range(6)])
for p in (5,7,11):
    row=[]
    for k in (1,2):
        for n in (1,2):
            if n*p**k>250: continue
            a1=A376462(n*p**k)-A376462(n*p**(k-1)); a2=A376462(n*p**k-1)-A376462(n*p**(k-1)-1)
            row.append(f"n={n},k={k}:({vp(a1,p)},{vp(a2,p)})")
    print(f"  A376462 p={p} (conj1,conj2): "+" ".join(row))
