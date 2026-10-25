# A361711 at M=p^k (odd): a(M) = eps * (3M-1)/(2M) * C(3n,n) C(2n,n), n=(M-1)/2. Factor-by-factor p-adic behaviour.
from math import comb
from fractions import Fraction
def vp(x,p):
    x=Fraction(x)
    if x==0: return 99
    n,d=x.numerator,x.denominator; v=0
    while n%p==0: n//=p; v+=1
    while d%p==0: d//=p; v-=1
    return v
def padic_unit_mod(x,p,e):  # x rational p-adic unit -> residue mod p^e
    x=Fraction(x); return (x.numerator*pow(x.denominator,-1,p**e))%p**e
for p in (5,7,11,13):
  for k in (1,2,3):
    if p**k>3000: continue
    M,Mp=p**k,p**(k-1); n,np_=(M-1)//2,(Mp-1)//2
    C2,C2p=comb(2*n,n),comb(2*np_,np_)
    C3,C3p=comb(3*n,n),comb(3*np_,np_)
    f=Fraction(3*M-1,2*M); fp=Fraction(3*Mp-1,2*Mp)
    print(f"p={p} k={k}: v_p C(2n,n)={vp(C2,p)}  v_p C(3n,n)={vp(C3,p)} (expect k)  v_p((3M-1)/(2M))={vp(f,p)}")
    e=3*k
    phi=M-Mp
    # candidate constants
    r2=Fraction(C2,C2p); r3=Fraction(C3,C3p)/p; rf=f/fp
    sgn=(-1)**((p-1)//2)
    tests={
      "C(2n,n)/C(2n',n') vs sgn*4^phi": vp(r2-sgn*Fraction(4)**phi,p),
      "C(2n,n)/C(2n',n') vs 4^phi": vp(r2-Fraction(4)**phi,p),
      "[C(3n,n)/p^k]/[C(3n',n')/p^(k-1)] vs (27/4)^(phi/2)": vp(r3-Fraction(27,4)**(phi//2),p),
      "  ... vs -(27/4)^(phi/2)": vp(r3+Fraction(27,4)**(phi//2),p),
      "  ... vs sgn*(27/4)^(phi/2)": vp(r3-sgn*Fraction(27,4)**(phi//2),p),
      "  ... vs (27/4)^(phi/2) * 1/(something)?? just r3 mod p": padic_unit_mod(r3,p,1),
      "full ratio a(M)/a(M') - 1": vp(sgn*r2*r3*rf*(-1)**0 - 1, p),
    }
    for t,v in tests.items(): print("    ",t,"->",v)
    # product of the two binomial ratios vs 27^(phi/2)*4^(phi/2)= (108)^(phi/2)? test a few products
    prod=r2*r3
    for name,cand in (("sgn*(27)^(phi/2)*... 4^(phi) *(27/4)^(phi/2) = 27^(phi/2) 4^(phi/2)",sgn*Fraction(27*4)**(phi//2)),("27^(phi/2)*2^phi, no sign",Fraction(108)**(phi//2))):
        print("     r2*r3 vs",name,"->",vp(prod-cand,p))
    print("     (3M-1)/(2M) / (3M'-1)/(2M') - 1 valuation:", vp(rf-1,p), "  rf*(-1)?:", vp(rf+1,p))
