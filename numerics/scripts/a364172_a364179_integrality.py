# Integrality of A364172(n) = 3^n (6n)!/((3n)!(2n)! prod_{j<=n}(n+3j)) and A364179(n) = 2^n (10n)!/((5n)!(4n)! prod_{j<=n}(n+2j)).
# Closed forms derived by Legendre: v_3(A364172(n)) = (3n+s_3(n))/2 if 3∤n, = s_3(4m)/2 if n=3m;  v_2(A364179(n)) = 2n+s_2(n) (n odd), = s_2(3m) (n=2m).
# Also v_2(A364172(n)) = n + s_2(n) - v_2(prod_{j<=n}(n+3j)); test >= 0 and find its exact value pattern.
from math import factorial
from fractions import Fraction
def vq(x,q):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%q==0: a//=q; v+=1
    while b%q==0: b//=q; v-=1
    return v
def sq(x,q):
    s=0
    while x: s+=x%q; x//=q
    return s
def A364172(n):
    P=1
    for j in range(1,n+1): P*=(n+3*j)
    return Fraction(3**n*factorial(6*n),factorial(3*n)*factorial(2*n)*P)
def A364179(n):
    P=1
    for j in range(1,n+1): P*=(n+2*j)
    return Fraction(2**n*factorial(10*n),factorial(5*n)*factorial(4*n)*P)
ok_int=all(A364172(n).denominator==1 and A364179(n).denominator==1 for n in range(1,201))
print("integers for n<=200:",ok_int)
ok3=all(vq(A364172(n),3)==((3*n+sq(n,3))//2 if n%3 else sq(4*(n//3),3)//2) for n in range(1,201))
ok2b=all(vq(A364179(n),2)==(2*n+sq(n,2) if n%2 else sq(3*(n//2),2)) for n in range(1,201))
print("v_3(A364172) closed form:",ok3,"; v_2(A364179) closed form:",ok2b)
v2=[vq(A364172(n),2) for n in range(1,65)]
print("v_2(A364172(n)), n=1..64:",v2)
print("min over q in {2,5,7,11,13} and n<=200 of v_q(A364172):",min(vq(A364172(n),q) for q in (2,5,7,11,13) for n in range(1,201)),
      "; of v_q(A364179):",min(vq(A364179(n),q) for q in (2,3,5,7,11,13) for n in range(1,201)))
