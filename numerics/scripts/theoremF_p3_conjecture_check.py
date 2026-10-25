# Conjectured p=3 theorem: a+b ≡ c (mod 3)  ⟹  A(3M) ≡ A(M) (mod 3^{3r}), r = 1+v_3(M).  Extended checks: r up to 4, more m.
# Also list the c=3 failures from the sweep range to see the c ≡ 0 rule.
from math import comb
def vp(x):
    if x==0: return 99
    v=0
    while x%3==0: x//=3; v+=1
    return v
def gb(e,i):
    num=1
    for t in range(i): num*=(e-t)
    den=1
    for t in range(1,i+1): den*=t
    return num//den
def A(a,b,c,N):
    K=c*N
    Acoef=[gb(a*N,i) for i in range(K+1)]; B=[gb(b*N,i)*(-1)**i for i in range(K+1)]
    return sum(Acoef[i]*B[K-i] for i in range(K+1))
tests=[(2,-1,1),(3,-1,2),(4,-1,3),(-1,2,1),(5,2,1),(1,1,2),(-4,0,2),(2,2,1),(-3,1,1),(0,2,2),(1,-1,3),(5,-2,3),(-2,-1,3)]
print("good class a+b≡c (mod 3): slack = v_3(A(3M)-A(M)) - 3r")
for (a,b,c) in tests:
    out=[]
    for (r,ms) in ((1,(1,2,4,5,7,8)),(2,(1,2,4,5)),(3,(1,2)),(4,(1,))):
        for m in ms:
            M=m*3**(r-1); N=3*M
            if c*N>400: continue
            out.append(f"r{r}m{m}:{vp(A(a,b,c,N)-A(a,b,c,M))-3*r:+d}")
    print(f"  ({a},{b},{c}) a+b-c={a+b-c}: "+" ".join(out))
print("c=3 failures in a,b in [-4,5] (r<=3, m in {1,2,4}):")
fails=[]
for a in range(-4,6):
    for b in range(-4,6):
        if (a,b)==(0,0): continue
        mn=99
        for r in (1,2,3):
            for m in (1,2,4):
                M=m*3**(r-1); N=3*M
                if 3*N>330: continue
                mn=min(mn,vp(A(a,b,3,N)-A(a,b,3,M))-3*r)
        if mn<0: fails.append(((a,b),mn,(a%3,b%3)))
print("  ",fails)
