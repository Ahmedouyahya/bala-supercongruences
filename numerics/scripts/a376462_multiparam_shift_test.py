# Which multi-parameter shifted statements hold?  F(n1..n6) = sum_{k,j>=0} C(n1,k)C(n2,k)C(n3+k,k)C(n4,k+j)C(n5,k+j)C(n6+j,j)  (all n_i >= 0 here).
# Test F(p n - e) ≡ F(n - e) (mod p^3) for shift vectors e in {0,1}^6 (e=1: a's shifted congruence; e=0: first congruence), random n.
import random, itertools
from math import comb
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def F(n):
    n1,n2,n3,n4,n5,n6=n
    tot=0
    for k in range(0,min(n1,n2,n4,n5)+1):
        t1=C(n1,k)*C(n2,k)*C(n3+k,k)
        if t1==0: continue
        for j in range(0,min(n4,n5)-k+1):
            t2=C(n4,k+j)*C(n5,k+j)*C(n6+j,j)
            if t2: tot+=t1*t2
    return tot
random.seed(7)
p=5
results={}
for e in itertools.product((0,1),repeat=6):
    mins=[]
    for trial in range(6):
        n=tuple(random.randint(1,3) for _ in range(6))
        A=F(tuple(p*x-ei for x,ei in zip(n,e))); B=F(tuple(x-ei for x,ei in zip(n,e)))
        if A==B: continue
        mins.append(vp(A-B,p)-3)
    results[e]=min(mins) if mins else None
good=[e for e,v in results.items() if v is not None and v>=0]
print("p=5: shift patterns e (1 = shifted by -1) with F(pn-e) ≡ F(n-e) mod p^3 in all random tests:")
for e in good: print("  ",e)
print("number of good patterns:",len(good),"of 64; e.g. all-ones:",results[(1,)*6]," all-zeros:",results[(0,)*6])
