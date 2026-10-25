# Validate the two bounds in the planned proof of Lemma B (A370092, p=2):
#  E_k(n) := sum_{j even} (-1)^(k-j) C(k,j) j^n (j^P - 1),  claim v2(E_k) >= n + v2(floor(k/2)!)
#  O_k(n) := sum_{j odd}  (-1)^(k-j) C(k,j) j^n (j^P - 1),  claim v2(O_k) >= m + 1 + v2(floor(k/2)!)   (P = 2^m)
# and the arithmetic inequality v2(floor(k/2)!) >= floor(k/3) except k in {3,6,7,15}; plus the finite check for k=15.
from math import comb, factorial
def v2(x):
    if x==0: return 999
    v=0
    while x%2==0: x//=2; v+=1
    return v
worstE=99; worstO=99; whereE=None; whereO=None
for m in range(2,9):
    P=2**m
    for k in range(0,61):
        vf=v2(factorial(k//2))
        for n in range(m+2, m+2+40):
            E=sum((-1)**(k-j)*comb(k,j)*j**n*(j**P-1) for j in range(0,k+1,2))
            O=sum((-1)**(k-j)*comb(k,j)*j**n*(j**P-1) for j in range(1,k+1,2))
            if E!=0:
                s=v2(E)-(n+vf)
                if s<worstE: worstE=s; whereE=(m,k,n,v2(E),n+vf)
            if O!=0:
                s=v2(O)-(m+1+vf)
                if s<worstO: worstO=s; whereO=(m,k,n,v2(O),m+1+vf)
print("even-part bound: min slack", worstE, "at (m,k,n,v2E,bound)=", whereE)
print("odd-part  bound: min slack", worstO, "at (m,k,n,v2O,bound)=", whereO)
exc=[k for k in range(0,400) if v2(factorial(k//2)) < k//3]
print("k with v2(floor(k/2)!) < floor(k/3):", exc)
exc2=[k for k in range(0,400) if v2(factorial(k//2))+1 < k//3]
print("k with v2(floor(k/2)!)+1 < floor(k/3):", exc2)
# exact odd-part valuations for the exceptional k, over many n and m (need >= m+1+floor(k/3))
for k in (3,6,7,15):
    mins={}
    for m in range(2,10):
        P=2**m
        mn=min(v2(sum((-1)**(k-j)*comb(k,j)*j**n*(j**P-1) for j in range(1,k+1,2))) - m for n in range(0,64))
        mins[m]=mn
    print(f"k={k}: min over n in [0,64) of v2(O_k) - m, per m: {mins}   (need >= {1+k//3})")
