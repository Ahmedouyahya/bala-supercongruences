# Independent re-review tests for notes/A352275-u_m-corollary-of-A333096-machine-proof.md
# Run: ~/venvs/general/bin/python -I numerics/rereview_short_A352275.py > numerics/out/rereview_short_A352275.txt
# Exact arithmetic only (ints / Fractions). Every block prints PASS/FAIL counts.
from math import comb, factorial, floor
from fractions import Fraction
import sys, time
t0=time.time()
PASS=0; FAIL=0
def chk(ok, msg):
    global PASS, FAIL
    if ok: PASS+=1
    else:
        FAIL+=1; print("  FAIL:", msg)
def vp(x,p):
    x=Fraction(x)
    if x==0: return None
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def gbinom(z,k):           # generalized binomial C(z,k), z any integer, k integer
    if k<0: return 0
    if z>=0: return comb(z,k)
    return (-1)**k*comb(k-z-1,k)
def coef(r,k):             # note's formula: [x^k] c^r = C(r+2k-1,k) - C(r+2k-1,k-1), =1 for k=0
    if k==0: return 1
    return gbinom(r+2*k-1,k)-gbinom(r+2*k-1,k-1)
def T(r,N): return sum(coef(r,k) for k in range(N+1))
# ---- truncated power series helpers (lists of ints/Fractions, index = degree) ----
D=16
def mul(a,b,D=D):
    c=[0]*(D+1)
    for i,x in enumerate(a[:D+1]):
        if x==0: continue
        for j,y in enumerate(b[:D+1-i]): c[i+j]+=x*y
    return c
def powser(a,e,D=D):
    r=[1]+[0]*D
    for _ in range(e): r=mul(r,a,D)
    return r
# ===== T1: coefficient identity against the actual series c(x)^r, r in [-15,15] =====
print("== T1: [x^k]c(x)^r vs C(r+2k-1,k)-C(r+2k-1,k-1) and r/(r+2k)C(r+2k,k) and r/(r+k)C(r+2k-1,k), r in [-15,15], k<=15 ==")
cat=[comb(2*k,k)//(k+1) for k in range(D+1)]            # c(x)
cinv=[1]+[-cat[k-1] for k in range(1,D+1)]              # 1/c = 1 - x c
# sanity: c*cinv = 1
chk(mul(cat,cinv)==[1]+[0]*D, "c * (1 - x c) != 1")
n1=n2=n3=0; skipped3=0
for r in range(-15,16):
    ser=powser(cat,r) if r>=0 else powser(cinv,-r)
    for k in range(D):
        f=coef(r,k); n1+=1
        chk(ser[k]==f, f"coef formula r={r} k={k}: series {ser[k]} formula {f}")
        if r+2*k!=0:
            alt=Fraction(r,r+2*k)*gbinom(r+2*k,k); n2+=1
            chk(alt==f, f"r/(r+2k)C(r+2k,k) r={r} k={k}: {alt} vs {f}")
        else: skipped3+=1
        if r+k!=0 and k>0:
            alt2=Fraction(r,r+k)*gbinom(r+2*k-1,k); n3+=1
            chk(alt2==f, f"r/(r+k)C(r+2k-1,k) (Epoch target form) r={r} k={k}: {alt2} vs {f}")
print(f"  checked {n1} coefficient identities, {n2} r/(r+2k) forms ({skipped3} skipped with r+2k=0), {n3} r/(r+k) forms")
# ===== T2: the §3 chain: [x^k]c^r = [X^k](1-X)(1+X)^{r+2k-1}; T(r,N) = [X^N](1-X)(1+X)^{r+2N+1}/(1+X+X^2) = [X^N] Q (1+X)^{r+2N} = FNat(r+2N,N) =====
print("== T2: §3 chain and FNat / Qseries transcription ==")
def onepX(A,D=D): return [gbinom(A,j) for j in range(D+1)]
inv_cyc=[[1,-1,0][j%3] for j in range(D+1)]            # 1/(1+X+X^2) = (1-X)/(1-X^3)
chk(mul([1,1,1]+[0]*(D-2),inv_cyc)==[1]+[0]*D, "1/(1+X+X^2) series wrong")
Q=mul([1,0,-1]+[0]*(D-2),inv_cyc)                       # (1-X^2)/(1+X+X^2)
def qCoeff(n): return 1 if n==0 else (2 if n%3==0 else -1)   # Lean Spec.lean l.348
chk(Q==[qCoeff(n) for n in range(D+1)], f"Qseries coefficients {Q[:10]} != Lean qCoeff")
chk(mul([1,1,1]+[0]*(D-2),Q)==[1,0,-1]+[0]*(D-2), "cyclo3*Qseries != 1-X^2")
def FNat(A,B):  # coeff_B( Q * (1+X)^A ), A any integer (Lean: A natural)
    s=0
    for j in range(B+1): s+=Q[j]*gbinom(A,B-j) if j<=D else 0
    return s
cnt=0; cntneg=0
for r in range(-15,16):
    for k in range(D):
        lhs=coef(r,k); rhs=mul([1,-1]+[0]*(D-1), onepX(r+2*k-1))[k]; cnt+=1
        chk(lhs==rhs, f"[X^k](1-X)(1+X)^(r+2k-1) r={r} k={k}: {rhs} vs {lhs}")
for N in range(0,D):
    for r in range(-3*N-2,16):
        lhs=T(r,N)
        rhsA=mul(mul([1,-1]+[0]*(D-1), onepX(r+2*N+1)), inv_cyc)[N]
        rhsB=FNat(r+2*N,N)
        chk(lhs==rhsA, f"T(r,N) vs [X^N](1-X)(1+X)^(r+2N+1)/(1+X+X^2) r={r} N={N}")
        chk(lhs==rhsB, f"T(r,N) vs FNat(r+2N,N) r={r} N={N}: {lhs} vs {rhsB}")
        cnt+=2
        if r+2*N<0: cntneg+=1
print(f"  checked {cnt} identities ({cntneg} with r+2N<0, i.e. (1+X)^A as a series with A<0)")
# a_gen bridge: a_m(n)=T(mn,n)=FNat((m+2)n,n)
chk(all(T(m*n,n)==FNat((m+2)*n,n) for m in range(-3,6) for n in range(1,D)), "a_gen_nat_eq_FNat bridge T(mn,n)=FNat((m+2)n,n)")
# ===== T3: beta(S,N) = [X^N] (1-2X)/((1-X)(1-X+X^2)) (1-X)^{-S} vs T(S-N,N), ALL integers S =====
print("== T3: beta(S,N) (Adamczewski / Fable `bet`) vs T(S-N,N) for S in [-40,40], N<=15 ==")
inv_1mXpX2=[[1,1,0,-1,-1,0][j%6] for j in range(D+1)]
chk(mul([1,-1,1]+[0]*(D-2),inv_1mXpX2)==[1]+[0]*D, "1/(1-X+X^2) series wrong")
G=mul(mul([1,-2]+[0]*(D-1), inv_1mXpX2), [1]*(D+1))   # (1-2X)/(1-X+X^2)/(1-X)
def beta(S,N):
    ser=[(-1)**j*gbinom(-S,j) for j in range(D+1)]     # (1-X)^{-S}
    return mul(G,ser)[N]
bad=[]
for S in range(-40,41):
    for N in range(0,D):
        if beta(S,N)!=T(S-N,N): bad.append((S,N))
chk(not bad, f"beta mismatches at (S,N) = {bad[:10]} ...")
print(f"  beta(S,N)=T(S-N,N) for all S in [-40,40], N in [0,15]: mismatches {len(bad)} (so it also holds for r=S-N< -N)")
# ===== T4: two-parameter theorem numerics =====
print("== T4: v_p(T(pr,pN)-T(r,N)) - 3(v+1), v=min(v_p(N),v_p(r)); r in [-N, 30], N in [1,30], p in {5,7,11,13} ==")
def vint(x,p):
    if x==0: return None
    v=0
    while x%p==0: x//=p; v+=1
    return v
for p in (5,7,11,13):
    worst=None; viol=0; tested=0; zero=0; vN_viol=0
    for N in range(1,31):
        for r in range(-N,31):
            if r==0: continue
            v=min(vint(N,p),vint(r,p))
            d=T(p*r,p*N)-T(r,N); tested+=1
            if d==0: zero+=1; continue
            val=vint(d,p); slack=val-3*(v+1)
            if slack<0: viol+=1
            if val-3*(vint(N,p)+1)<0: vN_viol+=1
            if worst is None or slack<worst[0]: worst=(slack,r,N,val,v)
    chk(viol==0, f"p={p}: {viol} violations of the two-parameter congruence")
    print(f"  p={p}: tested {tested} pairs (incl. r in [-N,-1]), zero differences {zero}, violations {viol}, min slack {worst[0]} at r={worst[1]},N={worst[2]} (val={worst[3]},v={worst[4]}); violations if v:=v_p(N) alone: {vN_viol}")
# the note's explicit example: p=5, S=11, N=10 (r=1): valuation 4
d=T(5,50)-T(1,10); print("  p=5,S=11,N=10 (r=1): v_5(T(5,50)-T(1,10)) =", vint(d,5), "(note says 4; 3(v_5(N)+1)=6, 3(v+1)=3)")
chk(vint(d,5)==4, "explicit example valuation")
# higher v cases
print("  higher-v spot checks (slack = v_p(diff)-3(v+1)):")
for p,N,r in ((5,25,25),(5,25,50),(5,50,50),(5,25,-25),(5,50,-25),(5,125,125),(5,125,-125),(5,125,250),(7,49,49),(7,49,-49),(7,49,98),(11,121,121)):
    v=min(vint(N,p),vint(r,p)); d=T(p*r,p*N)-T(r,N); val=vint(d,p)
    chk(val is None or val-3*(v+1)>=0, f"high-v case p={p} N={N} r={r}")
    print(f"    p={p} N={N} r={r}: v={v} val={val} slack={None if val is None else val-3*(v+1)}")
# r < -N range (note: 'numerically also holds for -3N <= r < -N, p=5, N<=14')
for p in (5,7):
    worst=None; viol=0; tested=0
    for N in range(1,15):
        for r in range(-3*N,-N):
            v=min(vint(N,p),vint(r,p)); d=T(p*r,p*N)-T(r,N); tested+=1
            if d==0: continue
            val=vint(d,p); slack=val-3*(v+1)
            if slack<0: viol+=1
            if worst is None or slack<worst[0]: worst=(slack,r,N,val,v)
    chk(viol==0, f"r<-N range p={p}: {viol} violations")
    print(f"  r in [-3N,-N), N<=14, p={p}: tested {tested}, violations {viol}, min slack {worst[0]} at r={worst[1]},N={worst[2]}")
# ===== T5: Lean-level lemma statement FNat(p(B+Y),pB) ≡ FNat(B+Y,B) mod p^(3(lev+1)), FNat computed from Q*(1+X)^A directly =====
print("== T5: FNat_scale_supercongruence as stated (B,Y naturals, p^lev | B,Y), FNat from the series definition ==")
Dbig=200
Qbig=[qCoeff(n) for n in range(Dbig+1)]
def FNat_big(A,B): return sum(Qbig[j]*comb(A,B-j) for j in range(B+1))
for p,lev in ((5,0),(5,1),(7,0),(7,1),(11,0)):
    viol=0; tested=0; worst=None
    for B in range(0,36):
        for Y in range(0,36):
            if B%p**lev or Y%p**lev: continue
            if p*B>Dbig: continue
            d=FNat_big(p*(B+Y),p*B)-FNat_big(B+Y,B); tested+=1
            if d==0: continue
            s=vint(d,p)-3*(lev+1)
            if s<0: viol+=1
            if worst is None or s<worst[0]: worst=(s,B,Y)
    chk(viol==0, f"FNat lemma p={p} lev={lev}: {viol} violations")
    print(f"  p={p} lev={lev}: tested {tested} (B,Y) pairs, violations {viol}, min slack {worst}")
# ===== T6: the Formal Conjectures definition u m n (floor/toNat) and the corollary =====
print("== T6: u m n from lean-targets/352275_4b1f2230.lean (floor of rational, toNat) ==")
def u_lean(m,n):
    if n==0: return 1
    s=0
    for k in range(m*n+1):
        q=Fraction(n,n+2*k)*comb(n+2*k,k)
        f=floor(q); s+=max(f,0)
    return s
def term_ok(n,k):
    q=Fraction(n,n+2*k)*comb(n+2*k,k)
    return q.denominator==1 and q>=0 and q==coef(n,k)
chk(all(term_ok(n,k) for n in range(1,41) for k in range(0,3*n+1)), "term n/(n+2k)C(n+2k,k) not a nonneg integer = [x^k]c^n for some n<=40,k<=3n")
chk(all(u_lean(m,n)==T(n,m*n) for m in (1,2,3) for n in range(0,31)), "u_lean(m,n) != T(n,mn)")
A352275=[1,4,64,1429,35072,898129,23571781,628750217,16965558016,461752375705,12652302369439,348552604899778,9644571491252069,267852878928912034,7462156684641697991,208446714456132946429,5836259481820028112640,163741162073796817779389,4602160147618819467316159]
chk([u_lean(2,n) for n in range(len(A352275))]==A352275, "u_2 != OEIS A352275 data (fetched 2026-10-15)")
chk(u_lean(2,1)==4 and u_lean(2,2)==64 and u_lean(2,3)==1429, "a_one/a_two/a_three of the Lean target")
A333093=[1,2,8,41,232,1377,8399,52138,327656,2077934,13270633,85226594,549837391,3560702069,23132584742,150695482041,984021596136,6438849555963,42208999230224,277144740254566,1822379123910857,11998811140766701,79095365076843134]
A352276=[1,9,625,58785,5986993,633580634,68611922731,7545931449401,839183314181297,94112350842056469,10623982584664109750,1205644823097085684641,137414820511792364274091,15718880489100999321142976,1803621273322664188151352631,207499462144488863314062180035]
chk([u_lean(1,n) for n in range(len(A333093))]==A333093, "u_1 != OEIS A333093 data")
chk([u_lean(3,n) for n in range(len(A352276))]==A352276, "u_3 != OEIS A352276 data")
print(f"  u_1(n) == OEIS A333093 for n <= {len(A333093)-1}:", [u_lean(1,n) for n in range(len(A333093))]==A333093)
print(f"  u_3(n) == OEIS A352276 for n <= {len(A352276)-1}:", [u_lean(3,n) for n in range(len(A352276))]==A352276)
print(f"  u_2(n) == OEIS A352275 for n <= {len(A352275)-1}: True" if [u_lean(2,n) for n in range(len(A352275))]==A352275 else "  u_2 vs OEIS: MISMATCH")
print("  corollary valuations v_p(u_m(np^k)-u_m(np^(k-1))) - 3k  (m in 1..3, p in {5,7,11}, n in {1,2,3}, k in {1,2}):")
viol=0; exact=0; tot=0
for m in (1,2,3):
    for p in (5,7,11):
        row=[]
        for k in (1,2):
            for n in (1,2,3):
                if n*p**k>400: continue
                # Theorem parameters: N=mnp^(k-1), r=np^(k-1), v=k-1
                N=m*n*p**(k-1); r=n*p**(k-1); v=k-1
                assert N>=1 and r>=-N and N%p**v==0 and r%p**v==0 and 3*(v+1)==3*k
                assert T(p*r,p*N)==u_lean(m,n*p**k) and T(r,N)==u_lean(m,n*p**(k-1))
                d=u_lean(m,n*p**k)-u_lean(m,n*p**(k-1)); val=vint(d,p); s=val-3*k; tot+=1
                if s<0: viol+=1
                if s==0: exact+=1
                row.append(f"n={n},k={k}:{s:+d}")
        print(f"    m={m} p={p}: "+" ".join(row))
chk(viol==0, f"corollary violations {viol}")
print(f"  total {tot} cases, violations {viol}, slack exactly 0 in {exact} cases")
d=u_lean(1,7)-u_lean(1,1); print("  sharpness example m=1,p=7,n=1,k=1: v_7 =", vint(d,7)); chk(vint(d,7)==3, "sharpness example")
print(f"\nSUMMARY: PASS {PASS}  FAIL {FAIL}   ({time.time()-t0:.1f}s)")
