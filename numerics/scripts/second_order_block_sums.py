# Second-order Wolstenholme-type block sums needed for a Beukers/Straub block induction with A=1 weights.
# (W1) sum'_{block p^s} 1/k ≡ 0 mod p^{2s};  (W2) sum' 1/k^2 ≡ 0 mod p^s;  (W3) sum' H'_k / k ≡ 0 mod p^s ?;  (W4) sum' H'_k/k^2 ?;  (W5) sum' (H'_k)^2/k ?
# where H'_k = sum_{p∤i<=k} 1/i, blocks [l p^s, (l+1)p^s).
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
for p in (5,7,11):
    Hp=[Fraction(0)]
    for i in range(1,3*p*p+1): Hp.append(Hp[-1]+(Fraction(1,i) if i%p else 0))
    for s in (1,2):
        for l in (0,1,2):
            lo=l*p**s; hi=(l+1)*p**s
            if hi>3*p*p: continue
            ks=[k for k in range(lo,hi) if k%p and k>0]
            W1=sum(Fraction(1,k) for k in ks); W2=sum(Fraction(1,k*k) for k in ks)
            W3=sum(Hp[k]/k for k in ks); W4=sum(Hp[k]/(k*k) for k in ks); W5=sum(Hp[k]**2/k for k in ks)
            print(f"p={p} s={s} l={l}: v(W1)-2s={vp(W1,p)-2*s} v(W2)-s={vp(W2,p)-s} v(W3)-s={vp(W3,p)-s} v(W4)-s={vp(W4,p)-s} v(W5)-s={vp(W5,p)-s}")
