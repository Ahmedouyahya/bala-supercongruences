# A376462(n) = CT[Lambda^n], Lambda = (1+u+v)(1+z)(1+u+z)(1+w)(1+v+w)/(u v z w): fast dict-polynomial check + Newton polytope data.
from math import comb
from collections import defaultdict
from itertools import product
def pmul(A,B):
    R=defaultdict(int)
    for ea,ca in A.items():
        for eb,cb in B.items():
            R[tuple(x+y for x,y in zip(ea,eb))]+=ca*cb
    return R
def padd(*fs):
    R=defaultdict(int)
    for f in fs:
        for e,c in f.items(): R[e]+=c
    return R
def mono(e,c=1): return {tuple(e):c}
one=mono((0,0,0,0)); U=mono((1,0,0,0)); V=mono((0,1,0,0)); Z=mono((0,0,1,0)); W=mono((0,0,0,1))
Lnum=pmul(pmul(pmul(pmul(padd(one,U,V),padd(one,Z)),padd(one,U,Z)),padd(one,W)),padd(one,V,W))
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
P=one; res=[]
for n in range(0,7):
    res.append((P.get((n,n,n,n),0), a(n)))
    P=pmul(P,Lnum)
print("CT[Lambda^n] vs A376462, n=0..6:", res, "ALL EQUAL" if all(x==y for x,y in res) else "MISMATCH")
supp=[e for e,c in Lnum.items() if c]
print("support size", len(supp), "; coefficient of uvzw:", Lnum[(1,1,1,1)])
import numpy as np
from scipy.spatial import ConvexHull
pts=np.array(supp,dtype=float); hull=ConvexHull(pts); eqs=hull.equations
def classify(x):
    vals=eqs[:,:4]@np.array(x,dtype=float)+eqs[:,4]
    if np.any(vals>1e-9): return 'outside'
    if np.any(np.abs(vals)<1e-9): return 'boundary'
    return 'interior'
latt=[x for x in product(range(3),repeat=4) if classify(x)!='outside']
inter=[x for x in latt if classify(x)=='interior']
print("Newton polytope: dim", hull.ndim, "; #facets", len(eqs), "; lattice points", len(latt), "; interior lattice points", inter)
# Hasse-Witt number at the interior point: coefficient of (uvzw)^(p-1) in Lnum^(p-1) == a(p-1); is it a p-adic unit?
for p in (5,7,11):
    print(f"p={p}: a(p-1) mod p = {a(p-1)%p} (Hasse-Witt invertible iff nonzero)")
