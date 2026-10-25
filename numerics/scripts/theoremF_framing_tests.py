# Theorem F (our re-derivation of the "coefficient-framing" claim): phi(x) = (1+x)^a (1-x)^b (a,b in Z), c>=0,
#   A(N) = [x^{cN}] phi(x)^N  satisfies  A(n p^r) == A(n p^{r-1}) (mod p^{3r}) for p >= 5.
# Sub-lemmas tested here:
#  (Q1) gamma_s := [y^s] phi(y)^M (M = n p^{r-1}) has v_p >= r-1-v_p(s)  when v_p(s) <= r-1
#  (Q2) for T == 0 mod p, e = v_p(T):  H_T := sum_{0<i<T, p∤i} 1/i == 0 (mod p^{2e});  H_T^± := sum (-1)^{i+1}/i == 0 (mod p^{2e}) when T even
#  (Q3) the theorem itself for many (a,b,c,p,n,r), and sharpness; plus instances: A333561 (3,-1,2), A333562 (4,-1,3), A119259 (2,-1,1), A352373 (-1,-3,1), A103885 (2,-2,1)/2.
from math import comb
from fractions import Fraction
import sys
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def gbinom(a,k):  # generalized binomial C(a,k), a integer (possibly negative)
    num=1
    for i in range(k): num*= (a-i)
    den=1
    for i in range(1,k+1): den*=i
    return num//den
def coeff_phi_pow(a,b,N,s):  # [y^s] (1+y)^{aN} (1-y)^{bN}
    return sum(gbinom(a*N,i)*gbinom(b*N,s-i)*(-1)**(s-i) for i in range(0,s+1))
def A(a,b,c,N): return coeff_phi_pow(a,b,N,c*N)
# (Q2)
print("(Q2) harmonic bounds:")
for p in (5,7,11,13):
    worst=99; worstpm=99
    for T in range(p, 60*p+1, p):
        e=vp(T,p)
        H=sum(Fraction(1,i) for i in range(1,T) if i%p); Hpm=sum(Fraction((-1)**(i+1),i) for i in range(1,T) if i%p)
        worst=min(worst, vp(H,p)-2*e)
        if T%2==0: worstpm=min(worstpm, vp(Hpm,p)-2*e)
    print(f"  p={p}: min v_p(H_T)-2e = {worst};  min over even T of v_p(H_T^±)-2e = {worstpm}")
# (Q1)
print("(Q1) v_p(gamma_s) >= r-1-v_p(s):")
for p in (5,7):
    worst=99
    for (a,b) in ((3,-1),(4,-1),(-1,-3),(2,-2),(1,1),(-2,5)):
        for r in (2,3):
            for n in (1,2):
                M=n*p**(r-1)
                for s in range(1, 3*M+1):
                    g=coeff_phi_pow(a,b,M,s)
                    if g==0: continue
                    a_s=vp(s,p)
                    if a_s<=r-1:
                        worst=min(worst, vp(g,p)-(r-1-a_s))
    print(f"  p={p}: min slack = {worst}")
# (Q3) theorem + instances
print("(Q3) Theorem F tests (v_p(A(np^r)-A(np^(r-1))) - 3r):")
cases=[(3,-1,2,'A333561'),(4,-1,3,'A333562'),(2,-1,1,'A119259'),(-1,-3,1,'A352373'),(2,-2,1,'2*A103885'),(1,1,1,'[x^N](1-x^2)^N'),(5,-2,2,'generic'),(-3,2,1,'generic'),(2,0,1,'C(2N,N)'),(7,-4,3,'generic')]
for a,b,c,name in cases:
    row=[]
    worst=99
    for p in (5,7,11,13):
        for r in (1,2):
            for n in (1,2):
                N=n*p**r
                if c*N>900: continue
                d=vp(A(a,b,c,N)-A(a,b,c,N//p),p)-3*r
                worst=min(worst,d); row.append(f"{p}^{r}n{n}:{d:+d}")
    print(f"  ({a},{b},{c}) {name}: min slack {worst} | "+" ".join(row))
print("p=3 check for A333561:", [vp(A(3,-1,2,3**r)-A(3,-1,2,3**(r-1)),3)-3*r for r in (1,2,3)])
# identity checks of the OEIS sequences
def A333561(n): return sum(comb(n+j-1,j)*2**j for j in range(2*n+1))
def A333562(n): return sum(comb(n+j-1,j)*2**j for j in range(3*n+1))
def A352373(n): return sum(comb(3*n-2*k-1,n-2*k)*comb(n+k-1,k) for k in range(n//2+1))
def A333565(n): return 2**n*comb(2*n,n)+3*sum((-1)**(n+k+1)*2**k*comb(2*k,k) for k in range(n))
def A119259(n): return A(2,-1,1,n)
print("instances match OEIS definitions (n=1..12):", all(A(3,-1,2,n)==A333561(n) for n in range(1,13)), all(A(4,-1,3,n)==A333562(n) for n in range(1,13)), all(A(-1,-3,1,n)==A352373(n) for n in range(1,13)), all(A333565(n)==2*A119259(n)-(-1)**n for n in range(1,13)))
