# Test '(26)-type' dual identities for A376462:  does a(n) equal a signed sum of the dual kernel (squares on the C(n+k,k) side)?
#   b(n)  := sum_{k,j} (-1)^(k+j) C(n+k,k)^2 C(n,k) C(n+k+j,k+j)^2 C(n,j)
#   c(n)  := sum_{j,k} (-1)^(j+k) C(n+j,j) C(n+j+k,k) L(n,j) L(n,k),  L(n,j)=C(n,j)C(n+j,j)   (reflected multinomial form)
#   d(n)  := sum_{k,j} (-1)^(k+j) C(n+k,k)^2 C(n,k) C(n,k+j)^2 C(n+j,j)   (mixed: squares flipped only on the k-part)
# and compare with a(n), (-1)^n a(n), a(n-1) etc.
from math import comb
def C(a,b): return comb(a,b) if 0<=b<=a else 0
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
def b(n): return sum((-1)**(k+j)*C(n+k,k)**2*C(n,k)*C(n+k+j,k+j)**2*C(n,j) for k in range(n+1) for j in range(n+1))
def L(n,j): return C(n,j)*C(n+j,j)
def c(n): return sum((-1)**(j+k)*C(n+j,j)*C(n+j+k,k)*L(n,j)*L(n,k) for j in range(n+1) for k in range(n+1))
def d(n): return sum((-1)**(k+j)*C(n+k,k)**2*C(n,k)*C(n,k+j)**2*C(n+j,j) for k in range(n+1) for j in range(n+1))
def e(n): return sum((-1)**(k+j)*C(n,k)**2*C(n+k,k)*C(n+k+j,k+j)**2*C(n,j) for k in range(n+1) for j in range(n+1))
print("n, a(n), b(n), c(n), d(n), e(n):")
for n in range(0,8): print(n, a(n), b(n), c(n), d(n), e(n))
print("b==a?", all(b(n)==a(n) for n in range(10)), " b==(-1)^n a?", all(b(n)==(-1)**n*a(n) for n in range(10)))
print("c==a?", all(c(n)==a(n) for n in range(10)), " c==(-1)^n a?", all(c(n)==(-1)**n*a(n) for n in range(10)))
print("d==a?", all(d(n)==a(n) for n in range(10)), " d==(-1)^n a?", all(d(n)==(-1)**n*a(n) for n in range(10)))
print("e==a?", all(e(n)==a(n) for n in range(10)), " e==(-1)^n a?", all(e(n)==(-1)**n*a(n) for n in range(10)))
# single-index duality test on the inner sums: W(n,j) = sum_k C(n-j,k) L(n,k) ; its dual?
