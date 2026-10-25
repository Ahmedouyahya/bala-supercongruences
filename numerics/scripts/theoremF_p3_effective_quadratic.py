# p=3: is  Q_T := N^2/2 [x^T]L^2 + N^3/6 [x^T]L^3  divisible by 3^{2r + v_3(T)} for all T == 0 mod 3  (the 'effective quadratic' bound)?
# Also the full tail  sum_{j>=2} N^j/j! [x^T] L^j  vs 3^{min(2r+v_3(T), 3r)}  (the bound (2) of Theorem F).
from fractions import Fraction
from math import factorial
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def L_coeffs(a,b,p,K): return [Fraction(0)]+[ (Fraction(a*(-1)**(j+1),j)-Fraction(b,j)) if j%p else Fraction(0) for j in range(1,K+1)]
def mul(A,B,K):
    R=[Fraction(0)]*(K+1)
    for i,x in enumerate(A):
        if x==0: continue
        for j,y in enumerate(B):
            if i+j>K: break
            R[i+j]+=x*y
    return R
p=3; K=81
for (a,b,name) in ((2,-1,'A119259/A333565'),(3,-1,'A333561'),(4,-1,'A333562'),(-1,-3,'A352373'),(1,-1,'A002003'),(5,-2,'generic')):
    L=L_coeffs(a,b,p,K); Lj=[None,L]
    for j in range(2,10): Lj.append(mul(Lj[-1],L,K))
    for r in (1,2):
        N=p**r
        worstQ=99; worstFull=99; where=None
        for T in range(p,K+1,p):
            e=vp(T,p)
            Q=Fraction(N**2,2)*Lj[2][T]+Fraction(N**3,6)*Lj[3][T]
            full=sum(Fraction(N**j,factorial(j))*Lj[j][T] for j in range(2,10))
            sQ=vp(Q,p)-(2*r+e); sF=vp(full,p)-min(2*r+e,3*r)
            if sQ<worstQ: worstQ=sQ; where=T
            worstFull=min(worstFull,sF)
        print(f"{name:18s} r={r}: min over T of v3(Q_T)-(2r+e) = {worstQ} (at T={where}); min of v3(tail)-min(2r+e,3r) = {worstFull}")
