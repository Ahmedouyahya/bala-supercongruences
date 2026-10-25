# p=3, r=1: verify the finite-field reduction
#   (A(3m) - A(m))/9  ≡  -m^2 * [x^{3cm}] ( phi(x^3)^m * (L(x)^2 + m*L(x^3)) )   (mod 3),
# with L = sum_{3∤i} l_i x^i / i, l_i = a(-1)^{i+1} - b, and then tabulate the obstruction as a function of (a mod 3, b mod 3, c, m mod 3).
from fractions import Fraction
from itertools import product
def gb(e,i):
    num=1
    for t in range(i): num*=(e-t)
    den=1
    for t in range(1,i+1): den*=t
    return num//den
def phi_pow(a,b,E,K):  # coefficients of (1+x)^{aE}(1-x)^{bE} up to x^K
    A=[gb(a*E,i) for i in range(K+1)]; B=[gb(b*E,i)*(-1)**i for i in range(K+1)]
    return [sum(A[i]*B[t-i] for i in range(t+1)) for t in range(K+1)]
def mul(A,B,K):
    R=[Fraction(0)]*(K+1)
    for i,x in enumerate(A):
        if x==0: continue
        for j,y in enumerate(B):
            if i+j>K: break
            R[i+j]+=x*y
    return R
def mod3(fr):
    fr=Fraction(fr); assert fr.denominator%3
    return (fr.numerator*pow(fr.denominator,-1,3))%3
p=3
bad=0; table={}
for c in (1,2):
    for a in range(-4,6):
        for b in range(-4,6):
            if (a,b)==(0,0): continue
            for m in (1,2,4,5):
                N=p*m; K=c*N
                A_N=phi_pow(a,b,N,K)[K]; A_M=phi_pow(a,b,m,c*m)[c*m]
                lhs=Fraction(A_N-A_M,9)
                L=[Fraction(0)]+[Fraction(a*(-1)**(i+1)-b,i) if i%3 else Fraction(0) for i in range(1,K+1)]
                L2=mul(L,L,K)
                L3x=[Fraction(0)]*(K+1)
                for i in range(1,K//3+1): L3x[3*i]=L[i]  # L(x^3)
                inner=[L2[t]+m*L3x[t] for t in range(K+1)]
                phi3=[Fraction(0)]*(K+1)
                g=phi_pow(a,b,m,c*m)
                for s in range(c*m+1): phi3[3*s]=g[s]
                rhs=-m*m*mul(phi3,inner,K)[K]
                if mod3(lhs)!=mod3(rhs): bad+=1
                table.setdefault((a%3,b%3,c),set()).add((m%3,mod3(lhs)))
print("formula mismatches:",bad)
print("obstruction (A(3m)-A(m))/9 mod 3, keyed by (a mod 3, b mod 3, c): {(m mod 3, value)}")
for key in sorted(table): print("  ",key, sorted(table[key]))
