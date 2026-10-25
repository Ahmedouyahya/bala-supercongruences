# Numerical checks of the exact Lean statements planned for TF3*.lean (p=3, (a,b,c)=(2,-1,1)).
from fractions import Fraction as Fr
from math import comb, factorial
P=3
def vp(x):
    x=Fr(x)
    if x==0: return 10**9
    a,b=x.numerator,x.denominator; v=0
    while a%P==0: a//=P; v+=1
    while b%P==0: b//=P; v-=1
    return v
def v3n(n):
    v=0
    while n%3==0: n//=3; v+=1
    return v
fails=0
def check(c,msg):
    global fails
    if not c: fails+=1; print("FAIL",msg)
# 1. S2: 3|N, N>0: V 3 (v3 N) (sum_{k<N,3∤k} 1/k^2 + N/3)
for N in range(3,400,3):
    S=sum(Fr(1,k*k) for k in range(1,N) if k%3)
    check(vp(S+Fr(N,3))>=v3n(N),("S2",N))
# 2. H: 3|N: V 3 (2 v3 N) (2 H_N - N^2/3)
H={}
for N in range(3,400,3):
    h=sum(Fr(1,k) for k in range(1,N) if k%3); H[N]=h
    check(vp(2*h-Fr(N*N,3))>=2*v3n(N),("H",N))
# 3. Hpm: 6|N: V 3 (2 v3 N) (sum (-1)^(i+1) hh i)
for N in range(6,400,6):
    s=sum(Fr((-1)**(i+1),i) for i in range(1,N) if i%3)
    check(vp(s)>=2*v3n(N),("Hpm",N))
# series
K=400
L=[Fr(0)]+[Fr(2*(-1)**(i+1)+1,i) if i%3 else Fr(0) for i in range(1,K+1)]
def mul(f,g,K):
    h=[Fr(0)]*(K+1)
    for i,x in enumerate(f):
        if x==0 or i>K: continue
        for j,y in enumerate(g):
            if i+j>K: break
            h[i+j]+=x*y
    return h
L2=mul(L,L,K); L3=mul(L2,L,K)
# 4. g_t: t>=1: V 3 1 (g_t - (4(-1)^t+1))
T=K//3
g=[Fr(0)]+[L2[3*t]/t for t in range(1,T+1)]
for t in range(1,T+1):
    check(vp(g[t]-(4*(-1)**t+1))>=1,("g",t))
# 5. cubic: V 3 1 ([L^3]_{3t} - L_t)
for t in range(1,T+1):
    check(vp(L3[3*t]-L[t])>=1,("cubic",t))
# 6. psi*(1-X^2) = 3X - X^2
psi=[Fr(0)]+[Fr(2*(-1)**(i+1)+1) for i in range(1,K+1)]
for n in range(K+1):
    lhs=psi[n]-(psi[n-2] if n>=2 else 0)
    rhs=(3 if n==1 else 0)-(1 if n==2 else 0)
    check(lhs==rhs,("psi",n))
# 7. L == X^2 u^2 mod 3 coefficientwise; G == 2X^2 u
u=[Fr(1) if n%2==0 else Fr(0) for n in range(K+1)]
u2=mul(u,u,K)
Lhat=[Fr(0),Fr(0)]+u2[:K-1]
for n in range(K+1): check(vp(L[n]-Lhat[n])>=1,("Lhat",n))
Ghat=[Fr(0),Fr(0)]+[2*x for x in u[:T-1]]
for n in range(T+1): check(vp(g[n]-Ghat[n])>=1,("Ghat",n))
# 8. Q = L - (psi-1) g, coefficients V 3 1
pm1=psi[:]; pm1[0]-=1
Q=[L[n]-x for n,x in enumerate(mul(pm1,g,T))]
for n in range(T+1): check(vp(Q[n])>=1,("Q",n))
# 9. Lemma A: coeff M (Phi * X G') = -M coeff M (Phi*(psi-1)*G), Phi = (1+x)^{2M}(1-x)^{-M}; arbitrary G
import random
def phiM(M,K):
    A=[Fr(comb(2*M,i)) for i in range(K+1)]
    B=[Fr(comb(M+i-1,i)) for i in range(K+1)]
    return mul(A,B,K)
for M in range(1,15):
    Gr=[Fr(random.randint(-9,9),random.randint(1,9)) for _ in range(M+1)]
    Ph=phiM(M,M)
    XG=[n*Gr[n] for n in range(M+1)]
    lhs=mul(Ph,XG,M)[M]
    rhs=-M*mul(Ph,mul(pm1[:M+1],Gr,M),M)[M]
    check(lhs==rhs,("lemmaA",M))
# 10. expansion: coeff (3t) E - (N^2/2)[L2]_{3t} - (N^3/6)[L3]_{3t} has V >= 3r, E = exp(N L)
def expser(F,K):
    # exp of series F with F[0]=0
    E=[Fr(0)]*(K+1); E[0]=Fr(1)
    for k in range(K):
        E[k+1]=sum((j+1)*F[j+1]*E[k-j] for j in range(k+1))/(k+1)
    return E
for M in range(1,13):
    N=3*M; r=1+v3n(M); KK=3*M
    E=expser([N*x for x in L[:KK+1]],KK)
    for t in range(1,M+1):
        R=E[3*t]-Fr(N*N,2)*L2[3*t]-Fr(N**3,6)*L3[3*t]
        check(vp(R)>=3*r,("expand",M,t))
# 11. theorem: V 3 (3r) (A(3M)-A(M)) with A(N)=coeff N Phi_N
for M in range(1,30):
    N=3*M; r=1+v3n(M)
    AN=phiM(N,N)[N]; AM=phiM(M,M)[M]
    check(vp(AN-AM)>=3*r,("thm",M))
# 12. 2*v3(l!) <= l-1
for l in range(1,200):
    check(2*v3n(factorial(l))<=l-1,("fact",l))
print("fails:",fails)
