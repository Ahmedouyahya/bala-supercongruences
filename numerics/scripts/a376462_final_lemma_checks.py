# Final checks before writing the general-r proof.
# (1) Beukers (10) failure: sum_{n<p^t} H'_n ≡ p^{t-1} (mod p^t)  [so (10) is false for k=0]; but Lemma 4(i) is true (checked elsewhere).
# (2) Ingredients of our proof of Lemma 4(i): tau_s(n) := sum'_{k in B_s(n)} k^{-2} ≡ 0 (mod p^s);  H'_{p^t-1-n} - H'_n ≡ -p^t sum'_{n<mu<p^t} mu^{-2} (mod p^{2t}).
# (3) Class S decoupling: P2 - 2 P1 + 2 P3 ≡ 0 (mod p^{2r}) where P1 = Σ S~(M) H'_{pk'}, P2 = 2 Σ S~(M) H'_{p(k'+j')}, P3 = -Σ S~(M) H'_{pj'}.
#     Equivalently T_S ≡ 3 P1 - P3.
# (4) Lemma P: sum_{u in (Z/p^v)^x} u^{-d} ≡ 0 (mod p^{v - e(d)}), e(d) = 0 if (p-1)∤d else 1+v_p(d).
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def vpi(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def C(a,b): return comb(a,b) if 0<=b<=a else 0
for p in (5,7):
    Hp=[Fraction(0)]
    for i in range(1,p**3+1): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    for t in (1,2):
        S=sum(Hp[n] for n in range(p**t))
        print(f"(1) p={p} t={t}: sum_{{n<p^t}} H'_n mod p^t = {(S.numerator*pow(S.denominator,-1,p**t))%p**t}  (p^(t-1)={p**(t-1)})")
    ok2a=all(vp(sum(Fraction(1,k*k) for k in range(n*p**s,(n+1)*p**s) if k%p and k>0),p)>=s for s in (1,2) for n in range(0,6))
    ok2b=all(vp((Hp[p**t-1-n]-Hp[n]) + p**t*sum(Fraction(1,mu*mu) for mu in range(n+1,p**t) if mu%p),p)>=2*t for t in (1,2) for n in range(p**t))
    print(f"(2) p={p}: tau_s(n)≡0 mod p^s: {ok2a}; reflection identity mod p^2t: {ok2b}")
    for (r,m) in ((2,1),(2,2),(3,1)):
        N=m*p**r; M=N//p
        if N>130: continue
        H2=[Fraction(0)]
        for i in range(1,N+1): H2.append(H2[-1]+(Fraction(1,i) if i%p else Fraction(0)))
        St=lambda k,j: C(M-1,k)**2*C(M+k-1,k)*C(M-1,k+j)**2*C(M+j-1,j)
        P1=sum(St(k,j)*H2[p*k] for k in range(M) for j in range(M-k))
        P2=sum(2*St(k,j)*H2[p*(k+j)] for k in range(M) for j in range(M-k))
        P3=sum(-St(k,j)*H2[p*j] for k in range(M) for j in range(M-k))
        print(f"(3) p={p} r={r} m={m}: v(P2-2P1+2P3)-2r = {vp(P2-2*P1+2*P3,p)-2*r:+d};  v(3P1-P3)-2r = {vp(3*P1-P3,p)-2*r:+d}")
    for v in (1,2):
        for d in (1,2,3,4,5,6,8,12):
            S=sum(pow(u,-d,p**v) for u in range(1,p**v) if u%p)%p**v
            e=0 if d%(p-1) else 1+vpi(d,p)
            print(f"(4) p={p} v={v} d={d}: v_p(sum u^-d) = {vpi(S,p) if S else 99} >= v-e(d) = {v-e}: {(vpi(S,p) if S else 99)>=v-e}")
