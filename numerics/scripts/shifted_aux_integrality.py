# (1) Is V(M) = sum_k C(M-1,k)^2 C(M+k,k) divisible by M for all M?  W(M)=V(M)/M first values + factorization hints.
# (2) A376462 analogue: V2(M) = sum_{k,j} C(M-1,k)^2 C(M+k,k) C(M-1,k+j)^2 C(M+j-1,j); also the j-side analogue V3(M) = sum C(M-1,k)^2 C(M+k-1,k) C(M-1,k+j)^2 C(M+j,j); divisible by M?
# (3) moment valuations of the model shifted terms t_M(k)=C(M-1,k)^2 C(M+k-1,k): mu_d(M) for d<=6 at M = m p^s.
from math import comb
from fractions import Fraction
from sympy import factorint
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
V=lambda M: sum(C(M-1,k)**2*C(M+k,k) for k in range(M))
print("(1) M | V(M) for M<=120:", all(V(M)%M==0 for M in range(1,121)))
print("    W(M)=V(M)/M, M=1..12:", [V(M)//M for M in range(1,13)])
print("    factorizations W(p^s) for p=5,7: ", {M:factorint(V(M)//M) for M in (5,25,7,49)})
V2=lambda M: sum(C(M-1,k)**2*C(M+k,k)*C(M-1,k+j)**2*C(M+j-1,j) for k in range(M) for j in range(M-k))
V3=lambda M: sum(C(M-1,k)**2*C(M+k-1,k)*C(M-1,k+j)**2*C(M+j,j) for k in range(M) for j in range(M-k))
print("(2) M | V2(M) for M<=45:", all(V2(M)%M==0 for M in range(1,46)), " M | V3(M):", all(V3(M)%M==0 for M in range(1,46)))
print("    V2(M)/M:", [V2(M)//M for M in range(1,9)], " V3(M)/M:", [V3(M)//M for M in range(1,9)])
print("(3) model moments mu_d(M)=sum k^d t_M(k): valuations (d=0..6) at M=m p^s")
for p in (5,7):
    for s in (1,2):
        for m in (1,2,3):
            M=m*p**s
            if M>150: continue
            mus=[sum(k**d*C(M-1,k)**2*C(M+k-1,k) for k in range(M)) for d in range(7)]
            print(f"   p={p} M={M} s={s}: {[vp(x,p) for x in mus]}")
