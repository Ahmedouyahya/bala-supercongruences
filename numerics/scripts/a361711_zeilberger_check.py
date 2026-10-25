# Independent verification of the Zeilberger certificate for F(n,k) = (-1)^k C(n,k)^2 C(n-2,k)  (A361711),
# of the resulting order-2 recurrence for a(n), and that the closed forms satisfy the same recurrence identically.
# Certificate produced by Maxima: maxima -b numerics/a361711_zeilberger.mac  (output: numerics/out/a361711_zeilberger_certificate.txt)
from sympy import symbols, sympify, cancel, together, gamma, Rational, gammasimp, expand_func
from math import comb, factorial
from fractions import Fraction
n,k,m=symbols('n k m')
txt=open(__file__.replace('a361711_zeilberger_check.py','out/a361711_zeilberger_certificate.txt')).read()
stmts=[s.strip() for s in txt.replace('\n','').split(';') if s.strip()]
R=sympify(stmts[0].replace('^','**')); cs=list(sympify(stmts[1].replace('^','**')))
def shiftn_ratio(i):
    r=1
    for t in range(i):
        mm=n+t; r*=((mm+1)/(mm+1-k))**2*(mm-1)/(mm-1-k)
    return r
Fk1_over_F=-((n-k)/(k+1))**2*(n-2-k)/(k+1)
lhs=sum(c*shiftn_ratio(i) for i,c in enumerate(cs)); rhs=R.subs(k,k+1)*Fk1_over_F-R
print("certificate rational identity:", cancel(together(lhs-rhs)))
Pnum=cancel(R*(n-k-1)*(n-k)*(n-k+1)**2*(n-k+2)**2/(k**3*(n-1)))
def F(N,K): return (-1)**K*comb(N,K)**2*comb(N-2,K) if 0<=K<=N-2 else 0
def G(N,K):
    if K>N or K<0: return Fraction(0)
    return Fraction((-1)**K*K**3*(N-1)*int(Pnum.subs({n:N,k:K}))*factorial(N)**2*factorial(N-2), factorial(K)**3*factorial(N-K+2)**2*factorial(N-K))
ok=all(sum(int(cs[i].subs(n,N))*F(N+i,K) for i in range(3))==G(N,K+1)-G(N,K) for N in range(2,40) for K in range(0,N+3))
print("identity at all integer points 0<=k<=n+2, 2<=n<40, with factorial-form G:", ok)
print("boundary G(n,0)=G(n,n+1)=0:", all(G(N,0)==0 and G(N,N+1)==0 for N in range(2,40)))
def a(N): return 1 if N==1 else sum(F(N,K) for K in range(0,N-1))
print("recurrence on a(n), n=2..150:", all(sum(int(cs[i].subs(n,N))*a(N+i) for i in range(3))==0 for N in range(2,150)))
def odd(t): return (-1)**t*gamma(3*t+2)/(gamma(t+1)*gamma(2*t+2))*gamma(2*t+1)/gamma(t+1)**2
def even(t): return (-1)**t*Rational(1,6)*(2*t-3)/(2*t-1)*gamma(3*t+1)/(gamma(t+1)*gamma(2*t+1))*gamma(2*t+1)/gamma(t+1)**2
for name,N,seq in (("odd",2*m+1,[odd(m),even(m+1),odd(m+1)]),("even",2*m,[even(m),odd(m),even(m+1)])):
    c=[ci.subs(n,N) for ci in cs]
    print(f"closed form satisfies recurrence ({name} N):", cancel(gammasimp(expand_func(sum(ci*s for ci,s in zip(c,seq))/seq[0]))))
print("initial values a(2),a(3):", a(2), a(3), "; closed:", (-1)**1*Rational(1,6)*Rational(-1,1)*comb(3,1)*comb(2,1), (-1)**1*comb(4,1)*comb(2,1))
