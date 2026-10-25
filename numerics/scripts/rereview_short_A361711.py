# Independent re-review tests for notes/A361711-proof.md
# Run: ~/venvs/general/bin/python -I numerics/rereview_short_A361711.py > numerics/out/rereview_short_A361711.txt
from math import comb, factorial, prod, gcd
from fractions import Fraction
import sys, time, re
t0=time.time()
PASS=0; FAIL=0
def chk(ok,msg):
    global PASS,FAIL
    if ok: PASS+=1
    else: FAIL+=1; print("  FAIL:",msg)
def vint(x,p):
    if x==0: return None
    v=0
    while x%p==0: x//=p; v+=1
    return v
def vfrac(x,p):
    x=Fraction(x)
    if x==0: return None
    return vint(x.numerator,p)-vint(x.denominator,p)
def primes(lim):
    s=[True]*(lim+1); s[0]=s[1]=False
    for i in range(2,int(lim**.5)+1):
        if s[i]:
            for j in range(i*i,lim+1,i): s[j]=False
    return [i for i in range(lim+1) if s[i]]
# ---------------- definitions ----------------
def F(n,k): return (-1)**k*comb(n,k)**2*comb(n-2,k) if (n>=2 and 0<=k<=n-2) else 0
def a_def(n):
    if n==1: return 1
    return sum(F(n,k) for k in range(0,n-1))
def a_odd(n):  # a(2n+1)
    return (-1)**n*comb(3*n+1,n)*comb(2*n,n)
def a_odd_bala(n): return (-1)**n*Fraction(3*n+1,2*n+1)*Fraction(factorial(3*n),factorial(n)**3)
def a_even(n):  # a(2n), n>=1
    return (-1)**n*Fraction(1,6)*Fraction(2*n-3,2*n-1)*comb(3*n,n)*comb(2*n,n)
def a_closed(M): return a_odd((M-1)//2) if M%2 else a_even(M//2)
# ===== T1: definition vs OEIS data (fetched 2026-10-15) and the note's listed terms =====
print("== T1: definition vs OEIS A361711 data ==")
OEIS=[1,1,-8,5,126,-168,-2400,4125,50050,-98098,-1100736,2339064,25069968,-56279520,-585307008,1367240589,13919870250,-33510798750,-335813478000,827780223270,8194328596740,-20587404077760,-201822515032320,515067876905400,5009403008531376,-12953308371172848]
chk([a_def(n) for n in range(1,len(OEIS)+1)]==OEIS, "a(n) by definition != OEIS data")
chk([a_def(n) for n in range(1,9)]==[1,1,-8,5,126,-168,-2400,4125], "note's listed terms")
print("  a(1..26) by definition == OEIS: True" if [a_def(n) for n in range(1,27)]==OEIS else "  MISMATCH")
# ===== T2: Lemma 1 closed forms =====
print("== T2: Lemma 1: a(2n+1)=(-1)^n C(3n+1,n)C(2n,n) (n<=200), Bala's form, even form (1<=n<=200) ==")
chk(all(a_def(2*n+1)==a_odd(n) for n in range(0,201)), "odd closed form")
chk(all(a_odd(n)==a_odd_bala(n) for n in range(0,201)), "Bala's odd form")
chk(all(a_def(2*n)==a_even(n) for n in range(1,201)), "even closed form")
chk(a_def(2)==1 and a_def(3)==-8 and a_even(1)==1 and a_odd(1)==-8, "initial values")
# ===== T3: Zeilberger certificate, re-parsed from numerics/out/a361711_zeilberger_certificate.txt =====
print("== T3: certificate ==")
import sympy as sp
n,k=sp.symbols('n k')
import os
txt=open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),'out','a361711_zeilberger_certificate.txt')).read()
parts=[s.strip() for s in txt.replace('\n','').split(';') if s.strip()]
R=sp.sympify(parts[0].replace('^','**'),locals={'n':n,'k':k})
cs=list(sp.sympify(parts[1].replace('^','**'),locals={'n':n,'k':k}))
c0n=-3*n*(n-1)*(3*n+1)*(3*n+2)*(3*n**2+4*n+2); c1n=-6*n*(6*n**3+12*n**2+5*n+1); c2n=-n**2*(n+2)**2*(3*n**2-2*n+1)
chk(all(sp.expand(cs[i]-c)==0 for i,c in enumerate((c0n,c1n,c2n))), "c_i in the note != certificate file")
# Appendix A polynomial, typed from the note
P_note=sp.sympify("84*n**8 - 234*k*n**7 + 520*n**7 + 261*k**2*n**6 - 1215*k*n**6 + 1306*n**6 - 135*k**3*n**5 + 1101*k**2*n**5 - 2590*k*n**5 + 1772*n**5 + 27*k**4*n**4 - 441*k**3*n**4 + 1934*k**2*n**4 - 3042*k*n**4 + 1454*n**4 + 63*k**4*n**3 - 606*k**3*n**3 + 1870*k**2*n**3 - 2183*k*n**3 + 752*n**3 + 60*k**4*n**2 - 434*k**3*n**2 + 1062*k**2*n**2 - 1000*k*n**2 + 268*n**2 + 26*k**4*n - 160*k**3*n + 344*k**2*n - 296*k*n + 80*n + 4*k**4 - 24*k**3 + 52*k**2 - 48*k + 16",locals={'n':n,'k':k})
R_note=k**3*(n-1)*P_note/((n-k-1)*(n-k)*(n-k+1)**2*(n-k+2)**2)
chk(sp.cancel(R-R_note)==0, "R(n,k) of the note (with Appendix A P) != certificate file")
P=sp.cancel(R*(n-k-1)*(n-k)*(n-k+1)**2*(n-k+2)**2/(k**3*(n-1)))
chk(sp.expand(P-P_note)==0, "P(n,k) Appendix A != file")
print("  degrees of P: in n", sp.degree(P,n), "in k", sp.degree(P,k))
# (i) rational-function certificate identity, built from scratch
Fsym=(-1)**k*sp.binomial(n,k)**2*sp.binomial(n-2,k)
def ratio_shift_n(i):   # F(n+i,k)/F(n,k) as rational function
    r=sp.Integer(1)
    for t in range(i):
        m=n+t; r*=((m+1)/(m+1-k))**2*((m-1)/(m-1-k))
    return r
ratio_shift_k=-((n-k)/(k+1))**2*((n-2-k)/(k+1))   # F(n,k+1)/F(n,k)
lhs=sum(c*ratio_shift_n(i) for i,c in enumerate(cs)); rhs=R.subs(k,k+1)*ratio_shift_k-R
chk(sp.cancel(sp.together(lhs-rhs))==0, "rational certificate identity")
# (ii) the polynomial identity of the note (Phi-form)
q0=(n-k+2)**2*(n-k+1)**2*(n-k)*(n-k-1)
poly_id=cs[0]*q0+cs[1]*(n+1)**2*(n-1)*(n-k+2)**2*(n-k)+cs[2]*(n+2)**2*(n+1)**2*n*(n-1)+(n-1)*(n-k+2)**2*(n-k)*P.subs(k,k+1)+k**3*(n-1)*P
chk(sp.expand(poly_id)==0, "polynomial identity (Phi-form) not identically 0")
print("  polynomial identity expand ==", sp.expand(poly_id))
chk(sp.expand(P.subs(k,n)-(n+2)**4*(n+1)**2*(3*n**2-2*n+1))==0, "P(n,n) formula")
# (iii) the five Phi-form identities as exact rationals at all 2<=n<=60, 0<=k<=n, and the telescoped identity
def Phi(N,K): return Fraction((-1)**K*factorial(N)**2*factorial(N-2), factorial(K)**3*factorial(N-K+2)**2*factorial(N-K))
Pf=sp.lambdify((n,k),P,'math'); Pint=lambda N,K: int(sp.Poly(P,n,k).eval({n:N,k:K}))
Ppoly=sp.Poly(P,n,k)
def Pval(N,K): return int(Ppoly.eval({n:N,k:K}))
csv=[sp.Poly(c,n) for c in cs]
def cval(i,N): return int(csv[i].eval(N))
def Gphi(N,K):   # G(n,k) = Phi k^3 (n-1) P(n,k), with G(n,n+1):=0
    if K>N: return Fraction(0)
    return Phi(N,K)*K**3*(N-1)*Pval(N,K)
bad=0; cnt=0
for N in range(2,61):
    for K in range(0,N+1):
        ph=Phi(N,K); cnt+=1
        ok = (F(N,K)==ph*((N-K+2)**2*(N-K+1)**2*(N-K)*(N-K-1))
          and F(N+1,K)==ph*((N+1)**2*(N-1)*(N-K+2)**2*(N-K))
          and F(N+2,K)==ph*((N+2)**2*(N+1)**2*N*(N-1))
          and (K>N-1 or Gphi(N,K+1)==-ph*(N-1)*(N-K+2)**2*(N-K)*Pval(N,K+1))
          and (cval(0,N)*F(N,K)+cval(1,N)*F(N+1,K)+cval(2,N)*F(N+2,K)==Gphi(N,K+1)-Gphi(N,K)))
        if not ok: bad+=1
        # where R is finite (K<=N-2), G = R*F agrees with the Phi-form
        if K<=N-2:
            Rv=Fraction(K**3*(N-1)*Pval(N,K),(N-K-1)*(N-K)*(N-K+1)**2*(N-K+2)**2)
            if Rv*F(N,K)!=Gphi(N,K): bad+=1
chk(bad==0, f"Phi-form identities / telescoped identity: {bad} failures")
print(f"  Phi-form + telescoped identities at {cnt} integer points (2<=n<=60, 0<=k<=n): failures {bad}")
chk(all(Gphi(N,0)==0 and Gphi(N,N+1)==0 for N in range(2,61)), "boundary G(n,0)=G(n,n+1)=0")
# supports
chk(all(F(N,K)==0 for N in range(2,40) for K in range(N-1,N+5)), "F(n,k)=0 for k>n-2")
chk(all(F(N+2,N)!=0 for N in range(2,40)), "F(n+2,n) nonzero (support of F(n+2,.) reaches k=n)")
# (iv) recurrence on a(n) from the definition, n=2..300
chk(all(cval(0,N)*a_def(N)+cval(1,N)*a_def(N+1)+cval(2,N)*a_def(N+2)==0 for N in range(2,301)), "recurrence on a(n) n<=300")
# (v) closed forms satisfy the recurrence: exact numeric n<=400 and symbolic (ratio as rational function of m)
chk(all(cval(0,N)*a_closed(N)+cval(1,N)*a_closed(N+1)+cval(2,N)*a_closed(N+2)==0 for N in range(2,401)), "closed forms satisfy recurrence numerically n<=400")
m=sp.symbols('m')
# ratios built from factorials explicitly: odd(m)=(-1)^m (3m+1)!/(m!(2m+1)!) * (2m)!/m!^2 ; even(m)=(-1)^m (1/6)(2m-3)/(2m-1) (3m)!/(m!(2m)!) (2m)!/m!^2
def ff(x,a):  # x!/(x-a)! rising, a>=0 integer : (x)(x-1)...(x-a+1)
    r=sp.Integer(1)
    for i in range(a): r*=(x-i)
    return r
# even(m+1)/odd(m):  (-1) * (1/6)(2m-1)/(2m+1) * [(3m+3)!/(3m+1)!] * [m!(2m+1)!/((m+1)!(2m+2)!)] * [(2m+2)!/(2m)!] * [m!^2/(m+1)!^2]
r_eo = -sp.Rational(1,6)*(2*m-1)/(2*m+1)*ff(3*m+3,2)*(1/((m+1)*(2*m+2)))*ff(2*m+2,2)/(m+1)**2
# odd(m+1)/odd(m): (-1) * [(3m+4)!/(3m+1)!] * [m!(2m+1)!/((m+1)!(2m+3)!)] * [(2m+2)!/(2m)!] * [m!^2/(m+1)!^2]
r_oo = -ff(3*m+4,3)/((m+1)*ff(2*m+3,2))*ff(2*m+2,2)/(m+1)**2
# odd(m)/even(m): [(-1)^m (3m+1)!/(m!(2m+1)!)] / [(-1)^m (1/6)(2m-3)/(2m-1) (3m)!/(m!(2m)!)]  = 6(2m-1)/(2m-3) * (3m+1)/(2m+1)
r_oe = 6*(2*m-1)/(2*m-3)*(3*m+1)/(2*m+1)
# even(m+1)/even(m): (-1)*[(2m-1)/(2m+1)]*[(2m-3)/(2m-1)]^-1 ... do it directly
r_ee = -((2*m-1)/(2*m+1))/((2*m-3)/(2*m-1))*ff(3*m+3,3)/((m+1)*ff(2*m+2,2))*ff(2*m+2,2)/(m+1)**2
# sanity of the ratio formulas numerically
for mm in range(2,8):
    chk(Fraction(a_even(mm+1))/Fraction(a_odd(mm))==Fraction(str(sp.nsimplify(r_eo.subs(m,mm)))), f"r_eo at m={mm}")
    chk(Fraction(a_odd(mm+1))/Fraction(a_odd(mm))==Fraction(str(sp.nsimplify(r_oo.subs(m,mm)))), f"r_oo at m={mm}")
    chk(Fraction(a_odd(mm))/Fraction(a_even(mm))==Fraction(str(sp.nsimplify(r_oe.subs(m,mm)))), f"r_oe at m={mm}")
    chk(Fraction(a_even(mm+1))/Fraction(a_even(mm))==Fraction(str(sp.nsimplify(r_ee.subs(m,mm)))), f"r_ee at m={mm}")
# odd N=2m+1: c0(N) + c1(N) even(m+1)/odd(m) + c2(N) odd(m+1)/odd(m) == 0
Nodd=2*m+1; exo=sp.cancel(sp.together(cs[0].subs(n,Nodd)+cs[1].subs(n,Nodd)*r_eo+cs[2].subs(n,Nodd)*r_oo))
Nev=2*m;  exe=sp.cancel(sp.together(cs[0].subs(n,Nev)+cs[1].subs(n,Nev)*r_oe+cs[2].subs(n,Nev)*r_ee))
chk(exo==0, f"closed forms satisfy recurrence symbolically (odd N): {exo}")
chk(exe==0, f"closed forms satisfy recurrence symbolically (even N): {exe}")
print("  symbolic recurrence residual (odd N, even N):", exo, exe)
chk(sp.discriminant(3*n**2-2*n+1,n)<0 and all(cval(2,N)!=0 for N in range(1,2001)), "c2(n) != 0 for n>=1")
# ===== T4: Lemma 2 =====
print("== T4: Lemma 2 (E1),(E2) exact for all odd primes p<=100 with p^k<=30000 (incl. p=3); floor claim ==")
PR=primes(100)
cntE=0; badE=[]
def Uset(p,M): return [u for u in range(1,(M+1)//2) if u%p]
for p in PR:
    if p==2: continue
    k=1
    while p**k<=30000:
        M,Mp=p**k,p**(k-1); nn,np_=(M-1)//2,(Mp-1)//2; U=Uset(p,M)
        PU=prod(U); Pminus=prod(u-M for u in U); Pplus=prod(u+M for u in U)
        E1 = comb(2*nn,nn)*PU == (-1)**((p-1)//2)*comb(2*np_,np_)*Pminus
        E2 = comb(3*nn+1,nn)*PU == comb(3*np_+1,np_)*Pplus
        star = a_odd(nn)*PU**2 == a_odd(np_)*prod(u*u-M*M for u in U)
        cntE+=1
        if not (E1 and E2 and star): badE.append((p,k,E1,E2,star))
        k+=1
chk(not badE, f"Lemma 2 / (★) failures: {badE}")
print(f"  (E1),(E2),(★) exact for {cntE} (p,k) pairs; failures {len(badE)}")
# floor claim: floor((p^k-1)/(2p^a)) == floor((p^(k-1)-1)/(2p^(a-1))) for a>=1
chk(all((p**k-1)//(2*p**a)==(p**(k-1)-1)//(2*p**(a-1)) for p in PR if p>2 for k in range(1,8) for a in range(1,k+3)), "floor claim")
chk(all(((p**k-p**(k-1))//2)%2==((p-1)//2)%2 for p in PR if p>2 for k in range(1,8)), "sign (-1)^(n-n') = (-1)^((p-1)/2)")
chk(all(3*((p**k-1)//2)+1==p**k+(p**k-1)//2 for p in PR if p>2 for k in range(1,6)), "3n+1 = M+n")
# (★) from the DEFINITION of a (not the closed form) for small M
chk(all(Fraction(a_def(p**k))/a_def(p**(k-1))==prod(1-Fraction(p**(2*k),u*u) for u in Uset(p,p**k)) for p in (3,5,7,11,13,17,19) for k in (1,2) if p**k<=400), "(★) from the definition, p^k<=400")
# ===== T5: Lemma 3 and the Theorem =====
print("== T5: Lemma 3 v_p(H2)-k and theorem slack v_p(a(p^k)-a(p^(k-1)))-3k, p<=100, p^k<=30000 ==")
def H2_val(p,k,extra=6):   # p-adic valuation of H2 via residues mod p^(k+extra); returns (val or None if >= k+extra)
    mod=p**(k+extra); M=p**k
    s=0
    for u in range(1,(M+1)//2):
        if u%p: s=(s+pow(u,-2,mod))%mod
    return vint(s,p) if s else None
def H2_frac(p,k): return sum(Fraction(1,u*u) for u in Uset(p,p**k))
rows=[]; viol3=0; violT=0; cnt=0
for p in PR:
    if p<5: continue
    k=1
    while p**k<=30000:
        M,Mp=p**k,p**(k-1); nn,np_=(M-1)//2,(Mp-1)//2
        v2=H2_val(p,k); 
        if p**k<=3000:
            vf=vfrac(H2_frac(p,k),p); chk(vf==v2, f"H2 valuation modular vs Fraction p={p} k={k}: {v2} vs {vf}")
        d=a_odd(nn)-a_odd(np_); vd=vint(d,p)
        s3=(v2-k) if v2 is not None else 99; sT=vd-3*k
        if s3<0: viol3+=1
        if sT<0: violT+=1
        # sharpness relation: v(a-a') = 2k + v(H2) when v(H2)<2k, and v_p(a(M'))=0, Kummer
        if v2 is not None and v2<2*k: chk(vd==2*k+v2, f"v(a-a')=2k+v(H2) p={p} k={k}")
        chk(vint(a_odd(np_),p)==0 and vint(comb(2*np_,np_),p)==0 and vint(comb(3*np_+1,np_),p)==0, f"Kummer claims p={p} k={k}")
        rows.append((p,k,s3,sT)); cnt+=1; k+=1
chk(viol3==0, f"Lemma 3 violations {viol3}"); chk(violT==0, f"Theorem violations {violT}")
print(f"  {cnt} (p,k) pairs; Lemma 3 violations {viol3}; Theorem violations {violT}")
print("  pairs with slack != 0 (p,k,v(H2)-k,v(a-a')-3k):", [r for r in rows if r[2]!=0 or r[3]!=0])
print("  note's list p in {5,11,...,43} slack 0 and p=7 slack 1 reproduced:", all((r[3]==(1 if r[0]==7 else 0)) for r in rows if r[0]<=43))
# p=7, k=1 example: v_7(49 H2)=4, v_7(49^2 e2)=5
U7=Uset(7,7); H2=sum(Fraction(1,u*u) for u in U7); e2=sum(Fraction(1,U7[i]**2*U7[j]**2) for i in range(len(U7)) for j in range(i+1,len(U7)))
print("  p=7,k=1: v_7(49 H2) =", vfrac(49*H2,7), " v_7(49^2 e2) =", vfrac(49**2*e2,7))
chk(vfrac(49*H2,7)==4 and vfrac(49**2*e2,7)==5, "p=7 k=1 example")
# Lemma 3 proof steps: 2H2 ≡ sum_units 1/v^2 ≡ sum_units v^2 (mod p^k); power-sum formula
for p in (5,7,11,13):
    for k in (1,2,3):
        M=p**k; units=[v for v in range(1,M) if v%p]
        S_inv=sum(pow(v,-2,M) for v in units)%M; S_sq=sum(v*v for v in units)%M
        formula=Fraction((M-1)*M*(2*M-1),6)-p**2*Fraction((p**(k-1)-1)*p**(k-1)*(2*p**(k-1)-1),6)
        chk(formula==sum(v*v for v in units), f"power-sum formula p={p} k={k}")
        chk(S_inv==S_sq, f"sum 1/v^2 ≡ sum v^2 mod p^k p={p} k={k}")
        chk((2*sum(pow(u,-2,M) for u in Uset(p,M))-S_inv)%M==0, f"2H2 ≡ full sum p={p} k={k}")
        chk(formula%M==0, f"formula ≡ 0 mod p^k p={p} k={k}")
# p=3: Lemma 3 and the Theorem fail
print("  p=3: (k, v_3(H2)-k, v_3(a(3^k)-a(3^(k-1)))-3k):", [(k, (99 if H2_val(3,k) is None else H2_val(3,k))-k, vint(a_odd((3**k-1)//2)-a_odd((3**(k-1)-1)//2),3)-3*k) for k in range(1,8)])
chk(all(H2_val(3,k)==k-1 for k in range(1,8)), "v_3(H2)=k-1")
chk(all(vint(a_odd((3**k-1)//2)-a_odd((3**(k-1)-1)//2),3)<3*k for k in range(1,8)), "p=3 statement false")
# ===== T6: §4 by-products =====
print("== T6: §4 by-products ==")
def unit_prod(p,k,sign,extra):
    M=p**k; mod=p**(3*k+extra); r=1
    for u in Uset(p,M): r=r*(1+sign*M*pow(u,-1,mod))%mod
    return r
badX=[];badY=[];slackY={};badH1=[]
for p in PR:
    if p<5 or p>60: continue
    k=1
    while p**k<=30000:
        M=p**k; phi=M-M//p; mod=p**(3*k+3)
        X=unit_prod(p,k,-1,3); Y=unit_prod(p,k,+1,3)
        vX=vint((X-pow(4,phi,mod))%mod,p); vY=vint((Y-pow(4,-phi,mod))%mod,p)
        vX=99 if vX is None else vX; vY=99 if vY is None else vY
        if vX<3*k: badX.append((p,k,vX))
        if vY<3*k: badY.append((p,k,vY))
        slackY[(p,k)]=vY-3*k
        # Lehmer-type: H1 ≡ -2q + p^k q^2 (mod p^(2k)), q=(2^phi-1)/p^k
        mod2=p**(2*k+2); q=(pow(2,phi,mod2*M)-1)//M
        H1=sum(pow(u,-1,mod2) for u in Uset(p,M))%mod2
        vH=vint((H1+2*q-M*q*q)%mod2,p); vH=99 if vH is None else vH
        if vH<2*k: badH1.append((p,k,vH))
        k+=1
chk(not badX, f"X ≡ 4^phi (mod p^3k) failures {badX}"); chk(not badY, f"Y ≡ 4^-phi failures {badY}"); chk(not badH1, f"Lehmer-type failures {badH1}")
print("  Y-congruence slack (v - 3k) where nonzero:", {pk:s for pk,s in slackY.items() if s!=0})
# Cai 2002 statement as transcribed: prod_{d|n} C(d-1,(d-1)/2)^{mu(n/d)} ≡ (-1)^{phi(n)/2} 4^{phi(n)} (mod n^3), odd n, 3∤n
def mu(n):
    r=1; d=2
    while d*d<=n:
        if n%d==0:
            n//=d
            if n%d==0: return 0
            r=-r
        d+=1
    if n>1: r=-r
    return r
def phi(n): return sum(1 for i in range(1,n+1) if gcd(i,n)==1)
badC=[]
for N_ in range(5,400,2):
    if N_%3==0: continue
    num=1; den=1
    for d in range(1,N_+1):
        if N_%d==0:
            e=mu(N_//d); c=comb(d-1,(d-1)//2)
            if e==1: num*=c
            elif e==-1: den*=c
    diff=Fraction(num,den)-(-1)**(phi(N_)//2)*4**phi(N_)
    ok=all((diff.numerator%q**(3*vint(N_,q))==0) and diff.denominator%q for q in primes(N_) if N_%q==0)
    if not ok: badC.append(N_)
chk(not badC, f"Cai statement (as transcribed) fails for n in {badC[:10]}")
print("  Cai 2002 statement as transcribed, odd n<400 with 3∤n (incl. composite): failures", badC[:10])
# extension data
print("  v_5(a(35)-a(7)) =", vint(a_def(35)-a_def(7),5))
chk(vint(a_def(35)-a_def(7),5)==5, "v_5(a(35)-a(7))=5")
ext=[(p,nn,vint(a_def(nn*p)-a_def(nn),p)) for p in (5,7,11) for nn in range(3,16,2)]
chk(all(v>=3 for _,_,v in ext), f"extension data {ext}")
print("  v_p(a(np)-a(n)) for p in {5,7,11}, odd 3<=n<=15:", ext)
# ===== T7: Lean cross-check of the closed form used in A361711.lean (A361711_odd_prod): a(2n+1) = prod_{i=1}^n (1 - M^2/i^2) =====
chk(all(Fraction(a_def(2*nn+1))==prod(1-Fraction((2*nn+1)**2,i*i) for i in range(1,nn+1)) for nn in range(0,60)), "A361711_odd_prod identity")
print(f"\nSUMMARY: PASS {PASS}  FAIL {FAIL}   ({time.time()-t0:.1f}s)")
