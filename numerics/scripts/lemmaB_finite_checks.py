# (1) Sanity test of the Amice-type bound used: f on Z_2 with f(a+2t)=sum c_i(a) t^i, c_i in Z_2  =>  v2(Delta^k f(0)) >= v2(floor(k/2)!)
# (2) Finite checks closing Lemma B for k in {3,6,7,15}: need v2(O_k(n,m)) >= m+1+floor(k/3) for all n>=0, m>=2.
#     Reduction: O_k = 2^(m+1) * [ S1 + 2*S2 ],  S1 = sum_t C(k,2t+1)(-1)^(k-2t-1) (1+2t)^n t(1+(2^m-1)t),
#     S2 = sum_t (...) (1+2t)^n R_m(t) with R_m in Z_2<t>  (Amice: v2(S2) >= v2(floor(k/2)!)).
#     So it suffices: v2(S1) >= floor(k/3)  (when floor(k/3) <= 1 + v2(floor(k/2)!), i.e. for k=3,6,7,15: 1<=1,2<=2,2<=2,5<=5 ok).
#     S1 mod 2^floor(k/3) depends on n mod 2^(floor(k/3)-2) (period of odd powers mod 2^floor(k/3)) and on (2^m-1) mod 2^floor(k/3).
from math import comb, factorial
import random
def v2(x):
    if x==0: return 999
    v=0
    while x%2==0: x//=2; v+=1
    return v
random.seed(1)
worst=99
for trial in range(200):
    deg=random.randint(0,8)
    c0=[random.randint(-50,50) for _ in range(deg+1)]; c1=[random.randint(-50,50) for _ in range(deg+1)]
    def f(j):
        a=j%2; t=(j-a)//2; cs=c1 if a else c0
        return sum(c*t**i for i,c in enumerate(cs))
    for k in range(0,45):
        ak=sum((-1)**(k-j)*comb(k,j)*f(j) for j in range(k+1))
        if ak: worst=min(worst, v2(ak)-v2(factorial(k//2)))
print("(1) Amice sanity: min over 200 random coset-polynomial f and k<45 of v2(a_k) - v2(floor(k/2)!) =", worst)
print("(2) finite checks of S1 for exceptional k:")
for k in (3,6,7,15):
    need=k//3; modn=2**max(need-2,0) if need>=2 else 1
    # also check directly with huge n range and all m up to 12, as a cross-check (exact integers)
    bad=[]
    for m in range(2,13):
        for n in range(0, 8*modn+8):
            S1=sum(comb(k,2*t+1)*(-1)**(k-2*t-1)*(1+2*t)**n*t*(1+(2**m-1)*t) for t in range(0,(k+1)//2))
            if v2(S1)<need: bad.append((m,n,v2(S1)))
    print(f"  k={k}: need v2(S1) >= {need}; violations over m=2..12, n<{8*modn+8}: {bad[:5]}  (count {len(bad)})")
    # exhaustive reduction: S1 mod 2^need depends on n mod 2^(need-2) [for need>=3] and on (2^m-1) mod 2^need
    # verify that claim directly by testing n and n+2^(need-2) give same residue, m and m' with same (2^m-1) mod 2^need give same residue
# direct exact confirmation of Lemma B at the exceptional k over a large grid (independent of the reduction)
for k in (3,6,7,15):
    need=1+k//3; bad=0
    for m in range(2,11):
        P=2**m
        for n in range(m+2, m+2+70):
            d=sum((-1)**(k-j)*comb(k,j)*j**n*(j**P-1) for j in range(k+1))
            if v2(d) < m+need: bad+=1
    print(f"  direct: k={k}, v2(b_k) >= m+{need} for m=2..10, 70 values of n each: violations={bad}")
