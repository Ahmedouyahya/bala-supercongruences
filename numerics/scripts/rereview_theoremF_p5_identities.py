#!/usr/bin/env python3
# Independent re-review of notes/TheoremF-coefficient-framing-proof.md (p >= 5 note): EXACT IDENTITIES.
#   Lemma 1 (reduced logarithm), Lemma 4 (coefficients of U^2, V^2, UV), Lemma 5 (Frobenius lifting),
#   the expansion (1) in section 4, the change-of-variables formula and S_c(n) identity of section 5(a),
#   the OEIS instance identities against statements/STATEMENTS.md data, the Lagrange-inversion /
#   o.g.f. identity of section 5(c) (series + sympy).
# All arithmetic exact (Fractions / sympy). Output: numerics/out/rereview_theoremF_p5_identities.txt
import os, re, random, sys, time
from fractions import Fraction as Fr
from math import comb, factorial

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repository root
OUT = os.path.join(ROOT, 'numerics/out/rereview_theoremF_p5_identities.txt')
LINES = []
def out(s=''):
    print(s); LINES.append(s)
NPASS = NFAIL = 0
def check(name, ok, detail=''):
    global NPASS, NFAIL
    if ok: NPASS += 1
    else: NFAIL += 1
    out(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ''))

# ---------- exact helpers ----------
def gbinom_list(e, K):
    """[C(e,i) for i<=K], e any integer (generalized binomial), incremental."""
    r = [1]
    for i in range(1, K+1):
        r.append(r[-1] * (e - i + 1) // i)
    return r
def phi_coeffs(a, b, N, K):
    """[y^s] (1+y)^{aN} (1-y)^{bN} for s<=K (integers)."""
    A = gbinom_list(a*N, K); B = gbinom_list(b*N, K)
    B = [B[i] * (-1)**i for i in range(K+1)]
    return [sum(A[i]*B[t-i] for i in range(t+1)) for t in range(K+1)]
def Acoef(a, b, c, N):
    K = c*N
    A = gbinom_list(a*N, K); B = gbinom_list(b*N, K)
    return sum(A[i] * B[K-i] * (-1)**(K-i) for i in range(K+1))
def smul(f, g, K):
    h = [Fr(0)]*(K+1)
    for i, x in enumerate(f[:K+1]):
        if x == 0: continue
        for j, y in enumerate(g[:K+1-i]):
            if y: h[i+j] += x*y
    return h
def sexp(f, K):
    assert f[0] == 0
    g = [Fr(0)]*(K+1); g[0] = Fr(1)
    for n in range(1, K+1):
        g[n] = sum(k*f[k]*g[n-k] for k in range(1, n+1)) / n
    return g
def sinv(f, K):
    g = [Fr(0)]*(K+1); g[0] = 1/Fr(f[0])
    for n in range(1, K+1):
        g[n] = -sum(Fr(f[k])*g[n-k] for k in range(1, min(n, len(f)-1)+1)) / Fr(f[0])
    return g
def U_series(p, K): return [Fr(0)] + [Fr(1, j) if j % p else Fr(0) for j in range(1, K+1)]
def V_series(p, K): return [Fr(0)] + [Fr((-1)**(j+1), j) if j % p else Fr(0) for j in range(1, K+1)]
def L_series(a, b, p, K):
    U = U_series(p, K); V = V_series(p, K)
    return [a*V[i] - b*U[i] for i in range(K+1)]

t0 = time.time()
out("Re-review of TheoremF-coefficient-framing-proof.md: exact identities. " + time.strftime('%Y-%m-%d %H:%M'))
out("=" * 100)

# ---------- Lemma 1 ----------
out("\n== Lemma 1: phi(x)^p = phi(x^p) * exp(p L(x)),  L = aV - bU   (tested to order 60, p = 3,5,7,11, a,b of all signs) ==")
K = 60
for p in (3, 5, 7, 11):
    allok = True; bad = []
    for (a, b) in [(1,0),(0,1),(2,-1),(-1,-3),(3,-1),(4,-1),(1,-1),(-2,5),(-3,-4),(5,7),(0,-2),(-1,0),(-5,-5)]:
        lhs = phi_coeffs(a, b, p, K)
        phi1 = phi_coeffs(a, b, 1, K)
        phixp = [Fr(0)]*(K+1)
        for s in range(K//p + 1): phixp[p*s] = Fr(phi1[s])
        E = sexp([p*x for x in L_series(a, b, p, K)], K)
        rhs = smul(phixp, E, K)
        if not all(Fr(lhs[i]) == rhs[i] for i in range(K+1)): allok = False; bad.append((a, b))
    check(f"Lemma 1 at p={p}, 13 pairs (a,b), order {K}", allok, f"bad pairs: {bad}")

# ---------- Lemma 4 / Lemma G ----------
out("\n== Lemma 4 (p>=5) / Lemma G (p=3): [x^T]U^2 = 2H_T/T, [x^T]V^2 = (-1)^T 2H_T/T, [x^T]UV = (1+(-1)^T) H_T^±/T for p | T ==")
for p in (3, 5, 7, 11):
    K = 30*p
    U = U_series(p, K); V = V_series(p, K)
    U2 = smul(U, U, K); V2 = smul(V, V, K); UV = smul(U, V, K)
    bad = []
    H = Fr(0); Hpm = Fr(0)
    for i in range(1, K+1):
        T = i
        if T % p == 0:
            c1 = U2[T] == 2*H/T
            c2 = V2[T] == (-1)**T * 2*H/T
            c3 = UV[T] == (1 + (-1)**T) * Hpm / T
            if not (c1 and c2 and c3): bad.append(T)
        if i % p:
            H += Fr(1, i); Hpm += Fr((-1)**(i+1), i)
    check(f"Lemma 4 at p={p}, all T = p, 2p, ..., {K}", not bad, f"bad T: {bad[:6]}")
    # also: the UV coefficient vanishes identically for odd T (claimed), not only via the formula
    oddzero = all(UV[T] == 0 for T in range(p, K+1, p) if T % 2 == 1)
    check(f"Lemma 4 at p={p}: [x^T]UV = 0 for odd T", oddzero)

# ---------- Lemma 5 ----------
out("\n== Lemma 5: f(y)^{p^k} ≡ f(y^{p^t})^{p^{k-t}} (mod p^{k-t+1}), random integer f of degree 6 ==")
def polmul(f, g):
    h = [0]*(len(f)+len(g)-1)
    for i, x in enumerate(f):
        if x == 0: continue
        for j, y in enumerate(g):
            h[i+j] += x*y
    return h
def polpow(f, n):
    r = [1]; base = f
    while n:
        if n & 1: r = polmul(r, base)
        n >>= 1
        if n: base = polmul(base, base)
    return r
random.seed(20261015)
for p in (3, 5, 7):
    kmax = {3: 3, 5: 2, 7: 2}[p]
    for k in range(0, kmax+1):
        for t in range(0, k+1):
            allok = True; tight_seen = False
            for trial in range(4):
                f = [random.randint(-9, 9) for _ in range(7)]
                lhs = polpow(f, p**k)
                fsub = [0]*(6*p**t + 1)
                for i, x in enumerate(f): fsub[i*p**t] = x
                rhs = polpow(fsub, p**(k-t))
                n = max(len(lhs), len(rhs)); lhs += [0]*(n-len(lhs)); rhs += [0]*(n-len(rhs))
                mod = p**(k-t+1)
                if not all((x - y) % mod == 0 for x, y in zip(lhs, rhs)): allok = False
                if any((x - y) % (mod*p) != 0 for x, y in zip(lhs, rhs)): tight_seen = True
            check(f"Lemma 5 p={p} k={k} t={t} (4 random f)", allok, f"bound attained (fails mod p^{k-t+2}) in some trial: {tight_seen}")

# ---------- expansion (1) ----------
out("\n== Section 4, identity (1): A(N) - A(M) = sum_{s=0}^{cM-1} gamma_s * eps_{p(cM-s)}  (exact) ==")
for p in (5, 7, 3):
    for (a, b, c) in [(2,-1,1),(3,-1,2),(-1,-3,1),(4,-1,3),(-2,5,1),(1,1,1)]:
        for M in (1, 2, p, 2*p):
            N = p*M; K = p*c*M
            if K > 240: continue
            E = sexp([N*x for x in L_series(a, b, p, K)], K)    # exp(NL); E[T] = eps_T for T>=1
            gam = phi_coeffs(a, b, M, c*M)
            S = sum(gam[s]*E[p*(c*M-s)] for s in range(0, c*M))
            lhs = Acoef(a, b, c, N) - Acoef(a, b, c, M)
            check(f"(1) p={p} (a,b,c)=({a},{b},{c}) M={M}", Fr(lhs) == S, f"A(N)-A(M)={lhs}")

# ---------- change of variables ----------
out("\n== Section 5(a): change-of-variables formula [x^K]f = [z^K] f(x(z)) psi(z)^K (1 - z psi'/psi),  x = z/psi(z) ==")
def compose(f, x, K):
    res = [Fr(0)]*(K+1); powx = [Fr(1)] + [Fr(0)]*K
    for i, fi in enumerate(f[:K+1]):
        if fi: res = [res[j] + fi*powx[j] for j in range(K+1)]
        powx = smul(powx, x, K)
    return res
random.seed(7)
for psi in ([1, 1], [1, 2, 3], [1, -1, 0, 1], [1, 0, 0, 0, 5]):
    allok = True
    for trial in range(3):
        Kmax = 9
        f = [Fr(random.randint(-5, 5), random.randint(1, 4)) for _ in range(Kmax+1)]
        psiF = [Fr(v) for v in psi] + [Fr(0)]*(Kmax+1-len(psi))
        x = [Fr(0)] + sinv(psiF, Kmax)[:Kmax]          # z / psi(z)
        dpsi = [Fr(i*psi[i]) if i < len(psi) else Fr(0) for i in range(1, Kmax+1)] + [Fr(0)]
        zpsi_prime = [Fr(0)] + dpsi[:Kmax]                # z psi'(z)
        factor = smul([psiF[i] - zpsi_prime[i] for i in range(Kmax+1)], sinv(psiF, Kmax), Kmax)  # 1 - z psi'/psi
        fx = compose(f, x, Kmax)
        for Kc in range(0, Kmax+1):
            psiK = [Fr(1)] + [Fr(0)]*Kmax
            for _ in range(Kc): psiK = smul(psiK, psiF, Kmax)
            rhs = smul(smul(fx, psiK, Kmax), factor, Kmax)[Kc]
            if rhs != f[Kc]: allok = False
    check(f"change-of-variables formula, psi={psi}, random f, K<=9", allok)

out("\n== Section 5(a): S_c(n) = sum_{j=0}^{cn} 2^j C(n+j-1,j) = A_{(c+1,-1,c)}(n) ==")
for c in (1, 2, 3, 4, 5):
    ok = all(sum(2**j*comb(n+j-1, j) for j in range(c*n+1)) == Acoef(c+1, -1, c, n) for n in range(1, 26))
    check(f"S_{c}(n) = A_(({c+1},-1,{c}))(n) for 1<=n<=25", ok)

# ---------- OEIS data from STATEMENTS.md ----------
out("\n== Instance identities against statements/STATEMENTS.md data (last data term dropped: truncated in the file) ==")
TXT = open(os.path.join(ROOT, 'statements/STATEMENTS.md')).read()
def oeis_data(aid):
    m = re.search(r'## ' + aid + r' .*?\n- offset: (-?\d+),\d+\n- data: ([0-9,\-]+)', TXT, re.S)
    off = int(m.group(1)); data = [int(x) for x in m.group(2).strip(',').split(',')]
    return off, data[:-1]
off, d = oeis_data('A333561')
check(f"A333561 = A_(3,-1,2): offset {off}, {len(d)} terms", all(Acoef(3, -1, 2, n) == d[n-off] for n in range(off, off+len(d))), f"data[:5]={d[:5]}")
off, d = oeis_data('A333562')
check(f"A333562 = A_(4,-1,3): offset {off}, {len(d)} terms", all(Acoef(4, -1, 3, n) == d[n-off] for n in range(off, off+len(d))), f"data[:5]={d[:5]}")
off, d = oeis_data('A352373')
check(f"A352373 = A_(-1,-3,1): offset {off}, {len(d)} terms", all(Acoef(-1, -3, 1, n) == d[n-off] for n in range(off, off+len(d))), f"data[:5]={d[:5]}")
off, d565 = oeis_data('A333565')
check(f"A333565(n) = 2*A_(2,-1,1)(n) - (-1)^n: offset {off}, {len(d565)} terms", all(2*Acoef(2, -1, 1, n) - (-1)**n == d565[n-off] for n in range(off, off+len(d565))), f"data[:5]={d565[:5]}")
# A119259 is not in STATEMENTS.md; the OEIS formula line on A333565 says a(n) = 2*A119259(n) - (-1)^n, so from the data:
d119 = [(d565[n] + (-1)**n) for n in range(len(d565))]
check("A119259 implied by A333565 data is even-divisible and equals A_(2,-1,1)", all(x % 2 == 0 for x in d119) and all(x//2 == Acoef(2, -1, 1, n) for n, x in enumerate(d119)), f"implied A119259[:6]={[x//2 for x in d119[:6]]}")
check("A119259 = S_1(n) = sum_{j<=n} 2^j C(n+j-1,j) (Barry formula as quoted) vs A_(2,-1,1), n<=30", all(sum(2**j*comb(n+j-1, j) for j in range(n+1)) == Acoef(2, -1, 1, n) for n in range(1, 31)))
# A333565 ogf (1+4t)/((1+t) sqrt(1-8t)) vs data
K = len(d565) - 1
sq = [Fr(comb(2*n, n) * 2**n) for n in range(K+1)]                      # 1/sqrt(1-8t) = sum C(2n,n) 2^n t^n
ogf = smul(smul([Fr(1), Fr(4)] + [Fr(0)]*(K-1), sinv([Fr(1), Fr(1)], K), K), sq, K)
check(f"o.g.f. (1+4t)/((1+t)sqrt(1-8t)) reproduces A333565 data, {K+1} terms", all(ogf[n] == d565[n] for n in range(K+1)))
# A352373 vs the alternative OEIS formula sum_k C(3n-2k-1,n-2k) C(n+k-1,k)
check("A352373 formula sum_k C(3n-2k-1,n-2k)C(n+k-1,k) = A_(-1,-3,1), n<=30", all(sum(comb(3*n-2*k-1, n-2*k)*comb(n+k-1, k) for k in range(n//2+1)) == Acoef(-1, -3, 1, n) for n in range(1, 31)))
# section 6 remark: b=0 gives binomials (Jacobsthal-Kazandzidis consistency)
check("b=0: A_(a,0,c)(N) = C(aN, cN)", all(Acoef(a, 0, c, N) == comb(a*N, c*N) for a in (2, 3, 5) for c in (1, 2) for N in range(1, 15) if c <= a))

# ---------- Section 5(c): Lagrange inversion and the sympy identity ----------
out("\n== Section 5(c): x = t(1+x)^2/(1-x);  sum_N B(N) t^N = (1-x^2)/(1-3x), B = A_(2,-1,1);  2(1-x^2)/(1-3x) - 1/(1+t) = (1+4t)/((1+t)sqrt(1-8t)) ==")
K = 18
one = [Fr(1)] + [Fr(0)]*K
x = [Fr(0)]*(K+1)
for it in range(K+2):
    onepx = [one[i] + x[i] for i in range(K+1)]
    q = smul(smul(onepx, onepx, K), sinv([one[i] - x[i] for i in range(K+1)], K), K)
    x = [Fr(0)] + q[:K]
# check the functional equation
onepx = [one[i] + x[i] for i in range(K+1)]
q = [Fr(0)] + smul(smul(onepx, onepx, K), sinv([one[i] - x[i] for i in range(K+1)], K), K)[:K]
check("x(t) solves x = t(1+x)^2/(1-x) to order 18", x == q, f"x(t) = {[str(v) for v in x[:7]]}")
x2 = smul(x, x, K)
F = smul([one[i] - x2[i] for i in range(K+1)], sinv([one[i] - 3*x[i] for i in range(K+1)], K), K)
check("(1-x^2)/(1-3x) = sum_N A_(2,-1,1)(N) t^N to order 18 (Lagrange inversion step)", all(F[n] == Acoef(2, -1, 1, n) for n in range(K+1)), f"series={[int(v) for v in F[:8]]}")
G = [2*F[i] - sinv([Fr(1), Fr(1)], K)[i] for i in range(K+1)]
sq = [Fr(comb(2*n, n) * 2**n) for n in range(K+1)]
ogf = smul(smul([Fr(1), Fr(4)] + [Fr(0)]*(K-1), sinv([Fr(1), Fr(1)], K), K), sq, K)
check("2(1-x^2)/(1-3x) - 1/(1+t) = (1+4t)/((1+t)sqrt(1-8t)) as series to order 18", G == ogf)
try:
    import sympy as sp
    t = sp.symbols('t')
    X = ((1 - 2*t) - sp.sqrt(1 - 8*t)) / (2*(1 + t))
    expr = 2*(1 - X**2)/(1 - 3*X) - 1/(1 + t) - (1 + 4*t)/((1 + t)*sp.sqrt(1 - 8*t))
    simp = sp.simplify(sp.radsimp(sp.together(expr)))
    ser = sp.series(expr, t, 0, 12).removeO()
    xser = sp.series(X, t, 0, 8).removeO()
    xcoef = [xser.coeff(t, n) for n in range(8)]
    check("sympy: closed-form x(t) matches the series solution (8 terms)", all(sp.Integer(1)*xcoef[n] == x[n] for n in range(8)), f"closed-form coefficients {xcoef}")
    check("sympy: 2(1-x^2)/(1-3x) - 1/(1+t) - (1+4t)/((1+t)sqrt(1-8t)) simplifies to 0 (or has zero series to O(t^12))", simp == 0 or sp.expand(ser) == 0, f"simplify -> {simp}; series -> {sp.expand(ser)}")
    # also numerically at a few points
    vals = [abs(complex(expr.subs(t, v).evalf(30))) for v in (sp.Rational(1, 20), sp.Rational(1, 11), sp.Rational(-1, 7))]
    check("sympy numeric check at t = 1/20, 1/11, -1/7 (|expr| < 1e-20)", all(v < 1e-20 for v in vals), f"{vals}")
except Exception as ex:
    check("sympy available", False, repr(ex))

out("\n" + "=" * 100)
out(f"SUMMARY: {NPASS} passed, {NFAIL} failed; elapsed {time.time()-t0:.1f}s")
open(OUT, 'w').write("\n".join(LINES) + "\n")
