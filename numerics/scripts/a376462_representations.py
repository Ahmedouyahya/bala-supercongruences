# Representations of A376462 and pattern search.
from math import comb
from itertools import combinations_with_replacement
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
# (R1) A108625(n,n-k) = sum_j C(n,j) C(n+j,j) C(n-k,j) ?
ok1=all(A108625(n,n-k)==sum(comb(n,j)*comb(n+j,j)*comb(n-k,j) for j in range(n+1)) for n in range(12) for k in range(n+1))
print("(R1) A108625(n,n-k) = sum_j C(n,j)C(n+j,j)C(n-k,j):", ok1)
# (R2) symmetric double sum a(n) = sum_{j,k} C(n,j)C(n-j,k) * C(n,j)C(n+j,j) * C(n,k)C(n+k,k)
def a_sym(n): return sum(comb(n,j)*comb(n-j,k)*comb(n,j)*comb(n+j,j)*comb(n,k)*comb(n+k,k) for j in range(n+1) for k in range(n-j+1))
print("(R2) symmetric multinomial form:", all(a(n)==a_sym(n) for n in range(12)))
# (R3) a(n) = sum_j C(n,j)^2 C(n+j,j) * W(n,j),  W(n,j) = sum_k C(n-j,k) C(n,k) C(n+k,k): search closed form of W
def W(n,j): return sum(comb(n-j,k)*comb(n,k)*comb(n+k,k) for k in range(n-j+1))
print("W(n,j) table:", [[W(n,j) for j in range(n+1)] for n in range(5)])
# is W(n,j) = sum_k C(n,k) C(n+k,k) C(n-j,k) = sum_k C(n,k)C(n-j,k)C(n+k,n) a known Apery-like triangle? test W(n,j) == A108625(n, n-j)
print("W(n,j) == A108625(n,n-j):", all(W(n,j)==A108625(n,n-j) for n in range(10) for j in range(n+1)))
# single-sum pattern search with safe binomials
def C(a,b): return comb(a,b) if 0<=b<=a else 0
fac={'C(n,k)':lambda n,k:C(n,k),'C(n+k,k)':lambda n,k:C(n+k,k),'C(2k,k)':lambda n,k:C(2*k,k),'C(2k,n)':lambda n,k:C(2*k,n),'C(2n-k,n)':lambda n,k:C(2*n-k,n),
     'C(n+k,2k)':lambda n,k:C(n+k,2*k),'C(2n,k)':lambda n,k:C(2*n,k),'C(3k,k)':lambda n,k:C(3*k,k),'C(2n+k,k)':lambda n,k:C(2*n+k,k),'C(n+k,n)^2':lambda n,k:C(n+k,n)**2,
     'C(2n-2k,n-k)':lambda n,k:C(2*n-2*k,n-k),'C(n,2k)':lambda n,k:C(n,2*k),'4^k':lambda n,k:4**k,'2^k':lambda n,k:2**k,'(-1)^k':lambda n,k:(-1)**k}
T=11; tv=[a(n) for n in range(T)]; names=list(fac); found=[]
for r in (1,2,3,4):
    for combo in combinations_with_replacement(names,r):
        ok=True
        for n in range(T):
            s=0
            for k in range(0,2*n+2):
                t=1
                for nm in combo:
                    t*=fac[nm](n,k)
                    if t==0: break
                s+=t
            if s!=tv[n]: ok=False; break
        if ok: found.append(combo)
print("single-sum matches:", found if found else "none")
# Apery-like generating structure: a(n) vs A005258(n)^2 etc.
A5258=[sum(comb(n,k)**2*comb(n+k,k) for k in range(n+1)) for n in range(T)]
print("a(n)/A005258(n):", [tv[n]/A5258[n] for n in range(6)])
