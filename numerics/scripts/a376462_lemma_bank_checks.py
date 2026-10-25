# Numerical verification of the auxiliary lemmas for the general-r proof of a(mp^r-1) ≡ a(mp^{r-1}-1) (A376462).
# Notation: L_s = m p^s; Psi_s(n,j) = C(L_s-1,n)^2 C(-L_s-1,n)(-1)^n C(L_s-1,n+j)^2 C(-L_s,j)(-1)^j ;
#           Xi_s^{(d)}(q,q') = C(L_s-1,q)^2 C(-L_s-1,q)(-1)^q C(L_s-1,q+q'+d)^2 C(-L_s-1,q')(-1)^{q'}.
# (A) kernel tower:  Psi_s(q, p j1) ≡ Psi_{s-1}([q/p], j1) (mod p^s);  Psi_s(q,j) ≡ 0 (mod p^s) for p∤j;
#                    Xi_s^{(d)}(q,q') ≡ Xi_{s-1}^{(d')}([q/p],[q'/p]) (mod p^s), d' = [q0+q0'+d >= p].
# (B) moment kernels K_s^{[t]}(q) = sum_j j^t Psi_s(q,j) ≡ 0 (mod p^s) for t>=1.
# (C) Lemma Y: sum_{n in B_t(i), j in B_t(i'), p∤j, carryout_t(n,j)=c} sigma_s'(n)/j ≡ 0 (mod p^{2s'+t}).
# (D) Lemma B: sum_{k in B_t(i), j in B_t(i'), p∤k, p∤j, carryout_t=c} 1/(kj) ≡ 0 (mod p^t).
# (E) Lemma 4(i) general blocks: sum_{n in B_t(i)} sigma_s(n) H'_n ≡ 0 (mod p^{t+2s}).
# (F) Lemma 4(ii)': sum'_{k in B_t(i)} (1/k) H'_{k p^s} ≡ 0 (mod p^{t+2s})   (checked in lemma4ii_strength.py)
from math import comb
from fractions import Fraction
import sys
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def C(a,b):
    if b<0: return 0
    if a>=0: return comb(a,b) if b<=a else 0
    return (-1)**b*comb(b-a-1,b)
def carryout(n,j,t,p):
    q=p**t
    return 1 if (n%q)+(j%q)>=q else 0
for p in (5,7):
    LIM=p**4+p**3
    Hp=[Fraction(0)]
    for i in range(1,LIM+1): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    def sigma(s,n): return sum(Fraction(1,k) for k in range(n*p**s,(n+1)*p**s) if k%p and k>0)
    print(f"=== p={p} ===")
    # (A),(B)
    for m in (1,2):
        for s in (1,2):
            L=m*p**s; Lm=m*p**(s-1)
            Psi=lambda S,n,j: 0 if n+j>m*p**S-1 else C(m*p**S-1,n)**2*C(-m*p**S-1,n)*(-1)**n*C(m*p**S-1,n+j)**2*C(-m*p**S,j)*(-1)**j
            Xi=lambda S,q,q1,d: C(m*p**S-1,q)**2*C(-m*p**S-1,q)*(-1)**q*C(m*p**S-1,q+q1+d)**2*C(-m*p**S-1,q1)*(-1)**q1
            okA1=all(vp(Psi(s,q,p*j1)-Psi(s-1,q//p,j1),p)>=s for q in range(L) for j1 in range(0,Lm))
            okA2=all(vp(Psi(s,q,j),p)>=s for q in range(L) for j in range(1,L-q) if j%p)
            okA3=all(vp(Xi(s,q,q1,d)-Xi(s-1,q//p,q1//p,1 if (q%p)+(q1%p)+d>=p else 0),p)>=s for q in range(L) for q1 in range(L) for d in (0,1))
            okB=all(vp(sum(j**t*Psi(s,q,j) for j in range(0,L-q)),p)>=s for q in range(L) for t in (1,2,3))
            print(f" m={m} s={s}: (A1) Psi tower {okA1}; (A2) unscaled-j terms ≡0 mod p^s {okA2}; (A3) Xi tower with carry {okA3}; (B) moment kernels ≡0 mod p^s {okB}")
    # (C),(D),(E)
    for t in (1,2):
        for s1 in (0,1):
            for (i,i1) in ((0,0),(1,0),(0,1),(1,2)):
                if (max(i,i1)+1)*p**(t+s1)>LIM: continue
                res=[]
                for c in (0,1):
                    S=Fraction(0)
                    for n in range(i*p**t,(i+1)*p**t):
                        sg=sigma(s1,n)
                        if sg==0: continue
                        for j in range(i1*p**t,(i1+1)*p**t):
                            if j%p==0 or j==0: continue
                            if carryout(n,j,t,p)==c: S+=sg/j
                    res.append(vp(S,p)-(2*s1+t))
                print(f" (C) t={t} s'={s1} blocks({i},{i1}): slack vs p^(2s'+t) by carry c=0,1: {res}")
        for (i,i1) in ((0,0),(1,0),(1,2)):
            res=[]
            for c in (0,1):
                S=sum(Fraction(1,k*j) for k in range(i*p**t,(i+1)*p**t) if k%p for j in range(i1*p**t,(i1+1)*p**t) if j%p and carryout(k,j,t,p)==c)
                res.append(vp(S,p)-t)
            print(f" (D) t={t} blocks({i},{i1}): slack vs p^t by carry: {res}")
        for s1 in (1,2):
            for i in (0,1,2):
                if (i+1)*p**(t+s1)>LIM: continue
                S=sum(sigma(s1,n)*Hp[n] for n in range(i*p**t,(i+1)*p**t))
                print(f" (E) Lemma4(i) t={t} s={s1} i={i}: slack vs p^(t+2s) = {vp(S,p)-(t+2*s1)}")
    sys.stdout.flush()
