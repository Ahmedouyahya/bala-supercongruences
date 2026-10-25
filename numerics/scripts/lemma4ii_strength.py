# Is Beukers' Lemma 4(ii) actually mod p^{t+2s}?   S(t,s,i) := sum'_{k in B_t(i)} (1/k) H'_{k p^s}.
# Also Lemma 4(i) strength: sum_{n in B_t(i)} sigma_s(n) H'_n vs p^{t+2s}, and the model's stratified class-S sums.
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
for p in (5,7,11):
    LIM=p**3*2+5
    Hp=[Fraction(0)]
    for i in range(1,LIM+1): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else Fraction(0)))
    for s in (1,2):
        for t in (1,2):
            for i in (0,1):
                if (i+1)*p**(t+s)>LIM: continue
                S=sum(Fraction(1,k)*Hp[k*p**s] for k in range(i*p**t,(i+1)*p**t) if k%p and k>0)
                print(f"p={p} s={s} t={t} i={i}: v(sum'(1/k)H'_{{kp^s}}) = {vp(S,p)}  [Lemma 4(ii) says >= t+s={t+s}; t+2s={t+2*s}]")
