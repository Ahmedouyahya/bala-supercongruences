# Lemma B test: v2( k! (S(n+2^m,k) - S(n,k)) ) >= m + 1 + floor(k/3)  for m>=2, all k, n >= n0(m)?
# Uses k!S(n,k) = sum_j (-1)^(k-j) C(k,j) j^n (exact integers).
from math import comb
import sys
def v2(x):
    if x==0: return 999
    v=0
    while x%2==0: x//=2; v+=1
    return v
def kS(n,k): return sum((-1)**(k-j)*comb(k,j)*j**n for j in range(k+1))
KMAX=int(sys.argv[1]) if len(sys.argv)>1 else 70; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 260
for m in range(2,11):
    P=2**m; fails=[]; min_n_ok=None
    # for each n, check all k<=KMAX (k>n+P gives 0)
    first_good=None; last_bad=-1
    for n in range(0,NMAX+1):
        ok=True
        for k in range(0,KMAX+1):
            d=kS(n+P,k)-kS(n,k)
            if d==0: continue
            if v2(d) < m+1+k//3:
                ok=False; fails.append((n,k,v2(d),m+1+k//3))
        if not ok: last_bad=n
    print(f"m={m}: Lemma B holds for all n > {last_bad} (n<= {NMAX}, k<= {KMAX}); failures at small n: {fails[:8]}{' ...' if len(fails)>8 else ''}")
# sharper: does v2(k!(S(n+2^m,k)-S(n,k))) >= m + 2 + max(0, k-5) hold? and what is min over n>=n0 of v2 - m for each k?
print("min over n in [40,200] of v2(b_k) - m, for m=5,8 and k=0..40:")
for m in (5,8):
    P=2**m
    prof=[min(v2(kS(n+P,k)-kS(n,k)) for n in range(40,201)) - m for k in range(0,41)]
    print(f" m={m}: {prof}")
