# Test: v_p(a(p^k) - a(p^(k-1))) for A361711 (conjecture needs >= 3k, p>=5)
from math import comb
def a(n):
    if n==1: return 1
    return sum((-1)**k*comb(n,k)**2*comb(n-2,k) for k in range(0,n-1))
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
for p in [5,7,11,13,17]:
    for k in [1,2]:
        print(f"p={p} k={k}: v={vp(a(p**k)-a(p**(k-1)),p)} need>={3*k}")
