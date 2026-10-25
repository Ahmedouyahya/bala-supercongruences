#!/usr/bin/env python3
# Independent referee tests for notes/TheoremF-p3-proof.md (Theorem F_3 at p = 3).
# Written from scratch with exact rational arithmetic; it does NOT import or reuse the project's scripts.
# Run:  ~/venvs/general/bin/python -I numerics/referee_theoremF_p3.py > numerics/out/referee_theoremF_p3.txt
#
# Notation (as in the note): phi = (1+x)^a (1-x)^b, A(N) = [x^{cN}] phi^N, N = 3M, M = 3^{r-1} m (3 ∤ m),
# ell_i = a(-1)^{i+1} - b, L = sum_{3∤i} ell_i x^i / i, psi = sum_{i>=1} ell_i x^i, D = y d/dy,
# C = Cartier (3-section), lambda_M(f) = [y^{cM}] phi(y)^M f(y), g_t = [x^{3t}] L^2 / t.
import random, sys, time
from fractions import Fraction as Fr
from math import factorial

T0 = time.time()
INF = 10**9
FAILS = []          # (test, detail)
def check(ok, test, detail=""):
    if not ok:
        FAILS.append((test, detail))
    return ok

# ---------- 3-adic helpers ----------
def v3(x):
    x = Fr(x)
    if x == 0: return INF
    n, d, v = abs(x.numerator), x.denominator, 0
    while n % 3 == 0: n //= 3; v += 1
    while d % 3 == 0: d //= 3; v -= 1
    return v
def r3(x):                      # residue mod 3 of a 3-integral rational
    x = Fr(x)
    assert x.denominator % 3, ("not 3-integral", x)
    return (x.numerator * pow(x.denominator, -1, 3)) % 3
def cong(x, y, k):              # x ≡ y (mod 3^k) in Z_(3)
    return v3(Fr(x) - Fr(y)) >= k

# ---------- coefficients of phi^E ----------
def gbinom(n, k):               # generalized binomial, n any integer, k >= 0; exact integer
    if k < 0: return 0
    num = 1
    for i in range(k): num *= (n - i)
    return num // factorial(k)
def binom_series(n, K, sign=1):  # [x^i] (1 + sign x)^n, i <= K
    return [gbinom(n, i) * (sign ** i) for i in range(K + 1)]
def phi_pow(a, b, E, K):        # [y^s] (1+y)^{aE} (1-y)^{bE}, s <= K
    A = binom_series(a * E, K); B = binom_series(b * E, K, -1)
    return [sum(A[i] * B[s - i] for i in range(s + 1)) for s in range(K + 1)]
def Aval(a, b, c, N):
    K = c * N; A = binom_series(a * N, K); B = binom_series(b * N, K, -1)
    return sum(A[i] * B[K - i] for i in range(K + 1))

# ---------- power series (lists of Fractions; index = degree) ----------
def smul(f, g, K):
    h = [Fr(0)] * (K + 1)
    for i in range(min(len(f), K + 1)):
        x = f[i]
        if x == 0: continue
        for j in range(min(len(g), K + 1 - i)):
            y = g[j]
            if y: h[i + j] += x * y
    return h
def sadd(f, g, K):
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0) for i in range(K + 1)]
def sscale(f, s): return [s * x for x in f]
def sD(f): return [i * f[i] for i in range(len(f))]
def sexp(f, K):                 # exp of a series with f[0] = 0
    res = [Fr(0)] * (K + 1); res[0] = Fr(1)
    term = [Fr(1)] + [Fr(0)] * K
    for j in range(1, K + 1):
        term = sscale(smul(term, f, K), Fr(1, j))
        if all(x == 0 for x in term): break
        res = sadd(res, term, K)
    return res
def ell(a, b, i): return a * (-1) ** (i + 1) - b
def Lser(a, b, K): return [Fr(0)] + [Fr(ell(a, b, i), i) if i % 3 else Fr(0) for i in range(1, K + 1)]
def psiser(a, b, K): return [Fr(0)] + [Fr(ell(a, b, i)) for i in range(1, K + 1)]
def User(K): return [Fr(0)] + [Fr(1, i) if i % 3 else Fr(0) for i in range(1, K + 1)]
def Vser(K): return [Fr(0)] + [Fr((-1) ** (i + 1), i) if i % 3 else Fr(0) for i in range(1, K + 1)]
def cartier(f): return [f[3 * t] for t in range((len(f) - 1) // 3 + 1)]
def lam(gam, f, cM): return sum(gam[s] * (f[cM - s] if cM - s < len(f) else 0) for s in range(cM + 1))
def L2_at_multiples(a, b, cM):  # [x^{3t}] L^2 for t = 0..cM (only those coefficients)
    K = 3 * cM; L = Lser(a, b, K)
    out = [Fr(0)] * (cM + 1)
    for t in range(1, cM + 1):
        T = 3 * t
        out[t] = sum(L[i] * L[T - i] for i in range(1, T) if i % 3 and (T - i) % 3)
    return out
def gser(a, b, cM):
    L2 = L2_at_multiples(a, b, cM)
    return [Fr(0)] + [L2[t] / t for t in range(1, cM + 1)]

def classify(a, b, c):
    if c % 3 == 0: return "good:3|c"
    if (a + b - c) % 3 == 0: return "good:a+b=c"
    if a % 3 == 0 and b % 3 == 0: return "EXTRA:a=b=0"
    return "bad"

print("Independent referee tests for TheoremF-p3-proof.md (p = 3). Exact arithmetic throughout.")
print("=" * 100)

# =====================================================================================
print("\n[T0] Lemma 1 at p = 3: phi(x)^3 = phi(x^3) exp(3 L(x)) to degree 36")
for (a, b) in [(2, -1), (-1, -3), (1, 1), (4, 4), (-2, 3)]:
    K = 36
    lhs = [Fr(x) for x in phi_pow(a, b, 3, K)]
    ph1 = phi_pow(a, b, 1, K // 3)
    phx3 = [Fr(ph1[i // 3]) if i % 3 == 0 else Fr(0) for i in range(K + 1)]
    rhs = smul(phx3, sexp(sscale(Lser(a, b, K), 3), K), K)
    ok = lhs == rhs
    check(ok, "T0", f"(a,b)={(a,b)}")
    print(f"  (a,b)={(a,b)}: {'OK' if ok else 'FAIL'}")

# =====================================================================================
print("\n[T1] Lemma A: lambda_M(D g) = -M lambda_M((psi - c) g) exactly, random g; and lambda_M(psi - c) = 0")
random.seed(20261015)
nA = 0
for (a, b, c) in [(2, -1, 1), (3, -1, 2), (4, -1, 3), (-1, -3, 1), (1, -1, 2), (-2, 5, 3), (0, 3, 1)]:
    for M in (1, 2, 3, 5, 9):
        cM = c * M
        gam = phi_pow(a, b, M, cM)
        psi = psiser(a, b, cM)
        for trial in range(3):
            g = [Fr(random.randint(-9, 9), random.randint(1, 7)) for _ in range(cM + 1)]
            lhs = lam(gam, sD(g), cM)
            pc = [psi[i] - (c if i == 0 else 0) for i in range(cM + 1)]
            rhs = -M * lam(gam, smul(pc, g, cM), cM)
            check(lhs == rhs, "T1", f"{(a,b,c,M)} trial {trial}")
            nA += 1
        pc = [psi[i] - (c if i == 0 else 0) for i in range(cM + 1)]
        check(lam(gam, pc, cM) == 0, "T1b", f"{(a,b,c,M)}")
print(f"  {nA} random instances of Lemma A + 35 instances of lambda_M(psi-c)=0: " + ("all OK" if not [f for f in FAILS if f[0].startswith('T1')] else "FAILURES"))

# =====================================================================================
print("\n[T2] Lemma B: A(N) - A(M) = sum_{j=2}^{3cM} (N^j/j!) lambda_M(C(L^j)) exactly; C(L) = 0; lambda_M(C(L^j)) in Z_(3)")
for (a, b, c, M) in [(2, -1, 1, 1), (2, -1, 1, 2), (2, -1, 1, 3), (3, -1, 2, 2), (3, -1, 2, 3), (4, -1, 3, 2),
                     (-1, -3, 1, 3), (1, -1, 2, 3), (-2, 5, 3, 3), (0, 3, 1, 6), (-4, 2, 1, 4)]:
    N = 3 * M; cM = c * M; K = 3 * cM
    L = Lser(a, b, K)
    gam = phi_pow(a, b, M, cM)
    tot = Fr(0); Lj = [Fr(1)] + [Fr(0)] * K; integral = True
    check(all(x == 0 for x in cartier(L)), "T2:C(L)=0", f"{(a,b)}")
    for j in range(1, K + 1):
        Lj = smul(Lj, L, K)
        lj = lam(gam, cartier(Lj), cM)
        if v3(lj) < 0: integral = False
        if j >= 2: tot += Fr(N ** j, factorial(j)) * lj
    diff = Aval(a, b, c, N) - Aval(a, b, c, M)
    ok = (tot == diff) and integral
    check(ok, "T2", f"{(a,b,c,M)}")
    print(f"  (a,b,c,M)={(a,b,c,M)}: expansion exact {tot == diff}, all lambda_M(C(L^j)) 3-integral {integral}")

# =====================================================================================
print("\n[T3] Lemma C: v_3(N^j/j!) for N = 3^r m (3 ∤ m): j=2 -> 2r, j=3 -> 3r-1, j>=4 -> >= 3r; plus v_3(j!) = (j - s_3(j))/2")
okC = True
for r in (1, 2, 3, 4):
    for m in (1, 2, 4):
        N = 3 ** r * m
        for j in range(2, 60):
            v = v3(Fr(N ** j, factorial(j)))
            want = {2: v == 2 * r, 3: v == 3 * r - 1}.get(j, v >= 3 * r)
            okC &= want
            if not want: check(False, "T3", f"r={r} m={m} j={j} v={v}")
for j in range(1, 200):
    s3 = sum(int(d) for d in format(j, 'b')) if False else 0
    s = 0; x = j
    while x: s += x % 3; x //= 3
    okC &= (v3(factorial(j)) == (j - s) // 2 and (j - s) % 2 == 0)
# minimum slack at j = 4 and j = 5 (the binding cases):
print("  all OK" if okC else "  FAIL")
print("  slack v_3(N^j/j!) - 3r at j=4,5 for r=1:", [v3(Fr(3 ** 1 * 1 ** 1) ** j / factorial(j)) - 3 for j in (4, 5)], "(j=4,r=1 is tight)")

# =====================================================================================
print("\n[T4] Lemma D: (N^3/6) lambda_M(C(L^3)) ≡ (9M^3/2) lambda_M(L) (mod 3^{3r}); and C(L^3) ≡ L(y) (mod 3) coefficientwise")
for (a, b) in [(2, -1), (-1, -3), (1, -1), (3, 3), (-2, 5)]:
    K = 90; L = Lser(a, b, K)
    L3 = smul(smul(L, L, K), L, K)
    CL3 = cartier(L3)
    okmod = all(v3(CL3[t] - L[t]) >= 1 for t in range(len(CL3)))
    check(okmod, "T4:C(L^3)", f"{(a,b)}")
    rows = []
    for c in (1, 2, 3):
        for r in (1, 2):
            for m in (1, 2):
                M = 3 ** (r - 1) * m; N = 3 * M; cM = c * M
                if 3 * cM > K: continue
                gam = phi_pow(a, b, M, cM)
                d = Fr(N ** 3, 6) * lam(gam, CL3, cM) - Fr(9 * M ** 3, 2) * lam(gam, L, cM)
                ok = v3(d) >= 3 * r
                check(ok, "T4", f"{(a,b,c,r,m)} v={v3(d)}")
                rows.append(f"c{c}r{r}m{m}:{v3(d) - 3*r:+d}" if v3(d) < INF else f"c{c}r{r}m{m}:=0")
    print(f"  (a,b)={(a,b)}: C(L^3)≡L mod 3: {okmod}; slack v_3(diff)-3r: " + " ".join(rows))

# =====================================================================================
print("\n[T5] Lemma E: S_2 ≡ -3^{e-1} (mod 3^e), 2 S_1 ≡ 3^{2e-1} (mod 3^{2e}), S_2^± ≡ 0 (mod 3^e); exact valuations shown")
for e in range(1, 6):
    R = [u for u in range(1, 3 ** e) if u % 3]
    S1 = sum(Fr(1, u) for u in R); S2 = sum(Fr(1, u * u) for u in R)
    S2pm = sum(Fr((-1) ** (u + 1), u * u) for u in R); S1pm = sum(Fr((-1) ** (u + 1), u) for u in R)
    okA = cong(S2, -3 ** (e - 1), e); okB = cong(2 * S1, 3 ** (2 * e - 1), 2 * e); okCc = v3(S2pm) >= e
    check(okA and okB and okCc, "T5", f"e={e}")
    print(f"  e={e}: (a) {okA} [v3(S2)={v3(S2)}]  (b) {okB} [v3(S1)={v3(S1)}]  (c) {okCc} [v3(S2±)={v3(S2pm)}]   (info: v3(S1±)={v3(S1pm)})")

# =====================================================================================
print("\n[T6] Lemma F: T = l 3^e, 3∤l: H_T ≡ -3^{2e-1} (mod 3^{2e}) [v_3 = 2e-1]; T even: H_T^± ≡ 0 (mod 3^{2e})")
for e in range(1, 5):
    rows = []
    for l in (1, 2, 4, 5, 7, 8):
        T = l * 3 ** e
        H = sum(Fr(1, i) for i in range(1, T) if i % 3)
        Hpm = sum(Fr((-1) ** (i + 1), i) for i in range(1, T) if i % 3)
        okA = cong(H, -3 ** (2 * e - 1), 2 * e) and v3(H) == 2 * e - 1
        okB = (T % 2 == 1) or v3(Hpm) >= 2 * e
        check(okA and okB, "T6", f"e={e} l={l}")
        rows.append(f"l={l}:(a){'ok' if okA else 'FAIL'}" + (f",(b){'ok' if okB else 'FAIL'}[v={v3(Hpm)}]" if T % 2 == 0 else f",(odd T: v3(H±)={v3(Hpm)})"))
    print(f"  e={e}: " + "  ".join(rows))

# =====================================================================================
print("\n[T7] Lemma G: [x^T]U^2 = 2H_T/T, [x^T]V^2 = (-1)^T 2H_T/T, [x^T]UV = (1+(-1)^T) H_T^±/T for 3 | T, T <= 90")
K = 90; U = User(K); V = Vser(K); UU = smul(U, U, K); VV = smul(V, V, K); UV = smul(U, V, K)
okG = True
for T in range(3, K + 1, 3):
    H = sum(Fr(1, i) for i in range(1, T) if i % 3); Hpm = sum(Fr((-1) ** (i + 1), i) for i in range(1, T) if i % 3)
    okG &= (UU[T] == 2 * H / T) and (VV[T] == (-1) ** T * 2 * H / T) and (UV[T] == (1 + (-1) ** T) * Hpm / T)
check(okG, "T7")
print("  all OK" if okG else "  FAIL")

# =====================================================================================
print("\n[T8] Lemma H: g_t = [x^{3t}]L^2/t is 3-integral and g_t ≡ a^2(-1)^t + b^2 (mod 3), t <= 150; D g = C(L^2)")
for (a, b) in [(2, -1), (3, -1), (4, -1), (-1, -3), (1, -1), (0, 1), (2, 2), (3, 3), (-4, 5), (0, 3), (7, -5)]:
    tmax = 150
    g = gser(a, b, tmax)
    okI = all(v3(g[t]) >= 0 for t in range(1, tmax + 1))
    okR = okI and all(r3(g[t]) == (a * a * (-1) ** t + b * b) % 3 for t in range(1, tmax + 1))
    minv = min(v3(g[t]) for t in range(1, tmax + 1))
    L2 = L2_at_multiples(a, b, tmax)
    okD = all(t * g[t] == L2[t] for t in range(tmax + 1))
    check(okI and okR and okD, "T8", f"{(a,b)}")
    print(f"  (a,b)={(a,b)}: integral {okI} (min v3(g_t) = {minv}), residues {okR}, Dg=C(L^2) {okD}")

# =====================================================================================
print("\n[T9] Lemma J over F_3: all 27 residue triples (a,b,c). Series truncated at degree 60; polynomial identities exact.")
def pmul(p, q):                 # product in F_3[y], NOT trimmed (length len(p)+len(q)-1)
    h = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            h[i + j] = (h[i + j] + x * y) % 3
    return h
def pad(p, K): return [p[i] if i < len(p) else 0 for i in range(K + 1)]
def ptrim(p):
    p = [x % 3 for x in p]
    while len(p) > 1 and p[-1] == 0: p.pop()
    return p
KJ = 60
print("  (a,b,c) | class        | J(a) L=Dpsi,rat.form | psi,g rat.forms | stated identity | residual L-(psi-c)g = K(psi-c)? (all K) ")
extra_classes = []
for c in range(3):
    for a in range(3):
        for b in range(3):
            al = (a - b) % 3; be = (-(a + b)) % 3
            Lb = [0] + [(ell(a, b, i) * pow(i, -1, 3)) % 3 if i % 3 else 0 for i in range(1, KJ + 1)]
            pb = [0] + [ell(a, b, i) % 3 for i in range(1, KJ + 1)]
            gb = [0] + [(a * a * (-1) ** t + b * b) % 3 for t in range(1, KJ + 1)]
            Dp = [(i * pb[i]) % 3 for i in range(KJ + 1)]
            one_m_y2 = [1, 0, 2]
            ja_series = (Lb == Dp)
            ja_rat = (ptrim(pmul(Lb, pmul(one_m_y2, one_m_y2))[:KJ + 1]) == ptrim([0, al, (2 * be) % 3, al]))
            psi_rat = (ptrim(pmul(pb, one_m_y2)[:KJ + 1]) == ptrim([0, al, be]))
            g_rat = (ptrim(pmul(gb, one_m_y2)[:KJ + 1]) == ptrim([0, (b * b - a * a) % 3, (a * a + b * b) % 3]))
            pc = [(pb[i] - (c if i == 0 else 0)) % 3 for i in range(KJ + 1)]
            pg = pad(pmul(pc, gb), KJ)
            resid = [(Lb[i] - pg[i]) % 3 for i in range(KJ + 1)]
            Ks = [Kk for Kk in range(3) if resid == [(Kk * pc[i]) % 3 for i in range(KJ + 1)]]
            # stated identities
            stated = "n/a"
            if c % 3 and (a + b - c) % 3 == 0:
                lhs = pmul([(-c) % 3, al], [(b * b - a * a) % 3, (a * a + b * b) % 3])
                stated = "J(b) poly " + ("OK" if ptrim(lhs) == ptrim([al, c % 3, al]) else "FAIL") + ", series " + ("OK" if resid == [0] * (KJ + 1) else "FAIL")
                check(ptrim(lhs) == ptrim([al, c % 3, al]) and resid == [0] * (KJ + 1), "T9:J(b)", f"{(a,b,c)}")
            elif c % 3 == 0:
                K0 = 1 if a != b else 2
                lhs = pmul([al, be], [K0, (b * b - a * a) % 3, (a * a + b * b - K0) % 3])
                okp = ptrim(lhs) == ptrim([al, (2 * be) % 3, al])
                oks = resid == [(K0 * pc[i]) % 3 for i in range(KJ + 1)]
                stated = f"J(c) K0={K0} poly " + ("OK" if okp else "FAIL") + ", series " + ("OK" if oks else "FAIL")
                check(okp and oks, "T9:J(c)", f"{(a,b,c)}")
            cls = classify(a, b, c)
            if Ks and cls == "bad": extra_classes.append((a, b, c, Ks))
            if cls == "EXTRA:a=b=0": extra_classes.append((a, b, c, Ks))
            check(ja_series and ja_rat and psi_rat and g_rat, "T9:J(a)/forms", f"{(a,b,c)}")
            # consistency of the note's (ii) with the residual: in good classes a K must exist
            if cls.startswith("good"): check(bool(Ks), "T9:good-class-has-K", f"{(a,b,c)}")
            print(f"  {(a,b,c)} | {cls:12s} | {str(ja_series):5s} {str(ja_rat):5s}         | {str(psi_rat):5s} {str(g_rat):5s}     | {stated:34s} | K in {Ks}")
print("  Residue classes with 3 ∤ c, a+b ≢ c where the residual IS still K(psi-c):", [(a, b, c, Ks) for (a, b, c, Ks) in extra_classes if c % 3])

# =====================================================================================
print("\n[T10] Proposition I: v_3( A(N)-A(M) - (9M^3/2) lambda_M(L - (psi-c) g) ) - 3r  [need >= 0], with digit check of Remark 1")
propI_triples = [(2, -1, 1), (3, -1, 2), (4, -1, 3), (-1, -3, 1), (1, -1, 1), (1, -1, 2), (3, -1, 1), (-3, -2, 2),
                 (0, 1, 2), (1, 2, 1), (3, 0, 1), (3, 3, 2), (-2, 1, 2), (1, -1, 3), (-1, -1, 1), (5, 2, 2)]
for (a, b, c) in propI_triples:
    rows = []
    for r in (1, 2, 3):
        for m in (1, 2, 4):
            M = 3 ** (r - 1) * m; N = 3 * M; cM = c * M
            if c * N > 330: continue
            L = Lser(a, b, cM); psi = psiser(a, b, cM); g = gser(a, b, cM)
            pc = [psi[i] - (c if i == 0 else 0) for i in range(cM + 1)]
            f = sadd(L, sscale(smul(pc, g, cM), -1), cM)
            gam = phi_pow(a, b, M, cM)
            lamf = lam(gam, f, cM)
            diff = Aval(a, b, c, N) - Aval(a, b, c, M)
            d = diff - Fr(9 * M ** 3, 2) * lamf
            ok = v3(d) >= 3 * r and v3(lamf) >= 0
            # Remark 1: (A(N)-A(M))/3^{3r-1} ≡ -m^3 lambda_M(fbar) (mod 3)
            digit = r3(Fr(diff, 3 ** (3 * r - 1))); pred = (-m ** 3 * r3(lamf)) % 3
            ok &= (digit == pred)
            check(ok, "T10", f"{(a,b,c,r,m)} v={v3(d)} digit={digit} pred={pred}")
            rows.append((f"r{r}m{m}:{v3(d) - 3*r:+d}" if v3(d) < INF else f"r{r}m{m}:=0") + f"(digit {digit})")
    print(f"  {(a,b,c)} [{classify(a,b,c)}]: " + " ".join(rows))

# =====================================================================================
print("\n[T11] Theorem F_3: slack v_3(A(3M)-A(M)) - 3r; need >= 0 in good classes, >= -1 always. r in {1,2,3}, m in {1,2,4,5,7}")
thm_triples = [
    # (a+b ≡ c, 3 ∤ c)
    (2, -1, 1), (3, -1, 2), (-1, 2, 1), (-1, -1, 1), (-4, 2, 1), (0, 2, 2), (1, 1, 2), (-2, 1, 2), (5, -3, 2), (-5, 1, 2),
    (2, 2, 1), (-2, -2, 2), (4, 0, 1), (0, -4, 2), (7, -3, 1), (-4, -3, 2), (-1, 5, 1),
    # 3 | c
    (4, -1, 3), (1, -1, 3), (-1, -3, 3), (2, 1, 3), (-2, 5, 3), (1, 1, 3), (-4, -4, 3), (5, 0, 3), (0, -2, 3), (2, -1, 6), (1, -2, 6),
    # a ≡ b ≡ 0 (mod 3), 3 ∤ c, a+b ≢ c  (NOT covered by the statement of (ii), but by its proof)
    (3, 0, 1), (0, 3, 2), (3, 3, 1), (-3, 3, 2), (3, -3, 1), (-3, -3, 2), (6, -3, 1), (-6, 3, 2), (3, 6, 1),
    # bad classes
    (1, -1, 1), (1, -1, 2), (-1, -3, 1), (2, -1, 2), (3, -1, 1), (-3, -2, 2), (0, 1, 2), (1, 2, 1), (4, 4, 1), (-2, 3, 1), (5, 2, 2),
]
for (a, b, c) in thm_triples:
    cls = classify(a, b, c); rows = []; mn = INF
    for r in (1, 2, 3):
        for m in (1, 2, 4, 5, 7):
            M = 3 ** (r - 1) * m; N = 3 * M
            if c * N > 450: continue
            d = Aval(a, b, c, N) - Aval(a, b, c, M)
            s = v3(d) - 3 * r; mn = min(mn, s)
            rows.append(f"r{r}m{m}:{s:+d}" if s < 50 else f"r{r}m{m}:=0")
    need = 0 if cls != "bad" else -1
    check(mn >= need, "T11", f"{(a,b,c)} class {cls} min slack {mn}")
    print(f"  {(a,b,c)} [{cls:11s}] min slack {mn if mn < 50 else 'inf'}: " + " ".join(rows))
print("  (iii) examples v_3(A(3)-A(1)):", {t: v3(Aval(*t, 3) - Aval(*t, 1)) for t in [(-1, -3, 1), (1, -1, 1), (1, -1, 2)]}, "(note claims 2)")
# the 'sporadic coincidence' (-3,-2,2) of Remark 3, pushed further in m at r = 1
print("  (-3,-2,2), r=1, slack for m = 1..16 (3∤m):", [(m, v3(Aval(-3, -2, 2, 3 * m) - Aval(-3, -2, 2, m)) - 3) for m in range(1, 17) if m % 3])

# =====================================================================================
print("\n[T12] Context check (Corollary input from the p>=5 note): A119259(n) = sum_{j<=n} 2^j C(n+j-1,j) = A_{(2,-1,1)}(n), n <= 25")
from math import comb
okCor = all(sum(2 ** j * comb(n + j - 1, j) for j in range(0, n + 1)) == Aval(2, -1, 1, n) for n in range(1, 26))
check(okCor, "T12"); print("  OK" if okCor else "  FAIL")

# =====================================================================================
print("\n" + "=" * 100)
print(f"SUMMARY: {len(FAILS)} failing checks; elapsed {time.time() - T0:.1f}s")
for t, d in FAILS: print("  FAIL", t, d)
