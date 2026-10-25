# Unit-product principle and factorial-ratio towers (our own route for A364175/A364178 and Bober ratios).
# U(X) := prod_{k<=X, p∤k} k ; W_r := U(p^r).  (UP): N = n p^r, p>=5:  U(aN) == W_r^{an} (mod p^{3r}).
# (LF): prod_{p∤k<=N} (1 + cN/(dk)) == 1 (mod p^{3r}) for p ∤ d.
# Exact ratio identities: A364175: a(N)/a(M) = U(6N)/(U(3N)U(2N)U(N)) / prod_{p∤k<=N}(1+2N/(3k));
#                          A364178: a(N)/a(M) = U(10N)U(3N)/(U(6N)U(5N)U(N)^2) / prod_{p∤k<=N}(1+N/(2k)).
from fractions import Fraction
from math import factorial
from functools import reduce
import sys
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def U(X,p): return reduce(lambda r,k: r*k if k%p else r, range(1,X+1), 1)
def a364175(n):
    den=reduce(lambda r,k: r*(2*n+3*k), range(1,n+1), 1)
    return Fraction(3**n*factorial(6*n), factorial(3*n)*factorial(2*n)*den)
def a364178(n):
    den=reduce(lambda r,k: r*(n+2*k), range(1,n+1), 1)
    return Fraction(2**n*factorial(10*n)*factorial(3*n), factorial(6*n)*factorial(5*n)*factorial(n)*den)
print("first terms:", [a364175(n) for n in range(5)], [a364178(n) for n in range(4)])
def prod(it): return reduce(lambda x,y:x*y, it, Fraction(1))
for p in (5,7,11):
    for r in (1,2):
        for n in (1,2,3):
            N=n*p**r; M=N//p
            if 10*N>3500: continue
            W=U(p**r,p)
            up=min(vp(Fraction(U(a*N,p), W**(a*n))-1,p)-3*r for a in (1,2,3,5,6,10))
            lf=min(vp(prod(1+Fraction(c*N,d*k) for k in range(1,N+1) if k%p)-1,p)-3*r for (c,d) in ((2,3),(1,2),(1,1),(3,4)))
            prod23=prod(1+Fraction(2*N,3*k) for k in range(1,N+1) if k%p); prod12=prod(1+Fraction(N,2*k) for k in range(1,N+1) if k%p)
            id175 = a364175(N)/a364175(M) == Fraction(U(6*N,p), U(3*N,p)*U(2*N,p)*U(N,p))/prod23
            id178 = a364178(N)/a364178(M) == Fraction(U(10*N,p)*U(3*N,p), U(6*N,p)*U(5*N,p)*U(N,p)**2)/prod12
            r175=vp(a364175(N)/a364175(M)-1,p)-3*r; r178=vp(a364178(N)/a364178(M)-1,p)-3*r
            print(f"p={p} r={r} n={n}: (UP) slack {up}; (LF) slack {lf}; A364175 identity {id175}, ratio slack {r175}; A364178 identity {id178}, ratio slack {r178}")
print("Wilson prime power W_r == -1 mod p^r:", all((U(p**r,p)+1)%p**r==0 for p in (5,7,11) for r in (1,2,3)))
# ---- A364178 integrality: F(x)=floor(10x)+floor(3x)-floor(6x)-floor(5x)-floor(x); need F(x) >= eps, eps=1 only if x=r/q>=1/3 (and q-r even)
from math import floor
def F(x): return floor(10*x)+floor(3*x)-floor(6*x)-floor(5*x)-floor(x)
from fractions import Fraction as Fr
pts=sorted(set(Fr(i,d) for d in range(1,61) for i in range(0,d)))
zero=[x for x in pts if F(x)==0]; neg=[x for x in pts if F(x)<0]
print("A364178 F(x) negative anywhere (denominators<=60)?", neg[:5]); print("zero set of F (denominators<=60): min", min(zero), "max", max(zero), "; all zeros < 1/3 ?", all(x<Fr(1,3) for x in zero))
# exact piecewise structure: breakpoints at multiples of 1/10,1/6,1/5,1/3; evaluate just right of each breakpoint
bps=sorted(set([Fr(i,10) for i in range(10)]+[Fr(i,6) for i in range(6)]+[Fr(i,5) for i in range(5)]+[Fr(i,3) for i in range(3)]))
print("F on intervals:", [(str(b), F(b)) for b in bps])
# eps analysis: for odd q and 0<=r<q, eps=1 iff exists s in [1,r] with q | r+2s  <=>  q-r even and q<=3r  (q odd)
for q in (3,5,7,11,13,101):
    for rr in range(0,q):
        eps=int(any((rr+2*s)%q==0 for s in range(1,rr+1)))
        pred=int(rr>0 and (((q-rr)%2==0 and q<=3*rr) or (rr%2==0 and 2*q<=3*rr)))
        assert eps==pred, (q,rr,eps,pred)
        if eps: assert 3*rr>=q, (q,rr)
print("eps characterisation (q odd): eps=1 iff r>0 and [(q-r even and q<=3r) or (r even and 2q<=3r)]; and eps=1 => r/q>=1/3 -- verified for q in {3,5,7,11,13,101}")
# direct integrality check via valuations, fast
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 2000
def legendre(X,q):
    s=0
    while X: X//=q; s+=X
    return s
def sieve(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
def v_lin(n,q):  # v_q(prod_{j<=n}(n+2j)) = sum_k #{j<=n: q^k | n+2j}
    tot=0; qk=q
    while qk<=3*n:
        if q==2:
            if n%2==1: cnt=0
            else:
                # n+2j = 2(n/2 + j): count j<=n with q^k | 2(n/2+j)
                m=n//2; cnt=sum(1 for j in range(1,n+1) if (2*(m+j))%qk==0) if n<=400 else None
        else:
            inv2=pow(2,-1,qk); j0=(-n*inv2)%qk
            if j0==0: j0=qk
            cnt=0 if j0>n else (n-j0)//qk+1
        if cnt is None: return None
        tot+=cnt; qk*=q
    return tot
bad=[]; checked=0
for n in range(1,NMAX+1):
    for q in sieve(10*n):
        vl=v_lin(n,q)
        if vl is None: continue
        v=(n if q==2 else 0)+legendre(10*n,q)+legendre(3*n,q)-legendre(6*n,q)-legendre(5*n,q)-legendre(n,q)-vl
        checked+=1
        if v<0: bad.append((n,q,v))
print(f"A364178 integrality via valuations: n<={NMAX}, {checked} (n,q) pairs checked, violations: {bad[:5]} (count {len(bad)})")
# direct cross-check of integrality with exact Fractions for small n, and Radcliffe's A364175 re-check
print("A364178 exact integers for n<=120:", all(a364178(n).denominator==1 for n in range(0,121)))
print("A364175 exact integers for n<=120:", all(a364175(n).denominator==1 for n in range(0,121)))
def v_lin175(n,q):  # v_q(prod_{j<=n}(2n+3j)), q != 3
    tot=0; qk=q
    while qk<=5*n:
        inv3=pow(3,-1,qk); j0=(-2*n*inv3)%qk
        if j0==0: j0=qk
        tot+= 0 if j0>n else (n-j0)//qk+1; qk*=q
    return tot
bad175=[]
for n in range(1,NMAX+1):
    for q in sieve(6*n):
        if q==3: continue
        v=legendre(6*n,q)-legendre(3*n,q)-legendre(2*n,q)-v_lin175(n,q)
        if v<0: bad175.append((n,q,v))
print(f"A364175 valuations (q != 3) nonnegative for n<={NMAX}: violations {bad175[:3]} (count {len(bad175)})")
print("v_2 formula check (n odd: 2n+s_2(n); n even: s_2(3n/2)):", all(vp(a364178(n),2)==(2*n+bin(n).count('1') if n%2 else bin(3*n//2).count('1')) for n in range(1,40)))
