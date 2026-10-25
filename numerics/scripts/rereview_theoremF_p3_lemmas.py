#!/usr/bin/env python3
# Independent re-review of notes/TheoremF-p3-proof.md (Theorem F_3 at p = 3). Exact arithmetic throughout.
#   Lemma A (exact-form identity, random g), Lemma B (exact expansion), Lemma C, Lemma D, Lemma E (exact leading digits),
#   Lemma F (exact leading digit of H_T, H_T^± for even T), Lemma G at p = 3, Lemma H (g_t integrality and residues,
#   including t divisible by 3, 9, 27, 81), Lemma J (F_3[[y]] identities, all 27 residue classes), Proposition I as an
#   exact congruence mod 3^{3r} (r up to 4, negative a, b), Theorem F_3 (i)/(ii) with slack (r up to 4, m up to 8),
#   Remark 1's digit formula and the "A352373 at every tested (r,m)" sentence, Remark 3's sweep survivors,
#   and the Observation about residue classes outside (ii).
# Output: numerics/out/rereview_theoremF_p3_lemmas.txt
import os, sys, time, random
from fractions import Fraction as Fr
from math import comb, factorial

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repository root
OUT = os.path.join(ROOT, 'numerics/out/rereview_theoremF_p3_lemmas.txt')
LINES = []
def out(s=''):
    print(s); LINES.append(s)
NPASS = NFAIL = 0
def check(name, ok, detail=''):
    global NPASS, NFAIL
    if ok: NPASS += 1
    else: NFAIL += 1
    out(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ''))

P = 3
INF = 10**6
def vp(x, p=P):
    x = Fr(x)
    if x == 0: return INF
    a, b = x.numerator, x.denominator; v = 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
def fmt(v): return 'inf' if v >= INF//2 else f"{v:+d}"
def mod3(x):
    x = Fr(x); assert x.denominator % 3, x
    return (x.numerator * pow(x.denominator, -1, 3)) % 3
def vp_fact(j, p=P):
    v = 0; q = p
    while q <= j: v += j // q; q *= p
    return v
def gbinom_list(e, K):
    r = [1]
    for i in range(1, K+1): r.append(r[-1] * (e - i + 1) // i)
    return r
def phi_coeffs(a, b, N, K):
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
def ell(a, b, i): return a*(-1)**(i+1) - b
def L_series(a, b, K): return [Fr(0)] + [Fr(ell(a, b, i), i) if i % 3 else Fr(0) for i in range(1, K+1)]
def psi_series(a, b, K): return [Fr(0)] + [Fr(ell(a, b, i)) for i in range(1, K+1)]
def cartier(f, K):   # C(f) = sum f_{3t} y^t, t <= K
    return [f[3*t] if 3*t < len(f) else Fr(0) for t in range(K+1)]
def lam(gam, f, cM):  # lambda_M(f) = sum_{s<=cM} gamma_s f_{cM-s}
    return sum(Fr(gam[s]) * f[cM-s] for s in range(cM+1) if cM-s < len(f))
# harmonic tables (computed once, incrementally): Hs[T] = H_T, Hpm[T] = H_T^± for T <= TMAX
TMAX = 2700
Hs = [Fr(0)]*(TMAX+2); Hp = [Fr(0)]*(TMAX+2)
h = Fr(0); hp = Fr(0)
for i in range(1, TMAX+2):
    Hs[i] = h; Hp[i] = hp
    if i % 3: h += Fr(1, i); hp += Fr((-1)**(i+1), i)
def coefU2(T): return 2*Hs[T]/T                     # Lemma G, used only AFTER Lemma G is verified independently below
def coefV2(T): return (-1)**T * 2*Hs[T]/T
def coefUV(T): return (1 + (-1)**T) * Hp[T] / T
def direct_L2_coef(a, b, T):  # [x^T] L^2 by direct convolution (independent of Lemma G)
    return sum(Fr(ell(a, b, i), i) * Fr(ell(a, b, T-i), T-i) for i in range(1, T) if i % 3 and (T-i) % 3)

t0 = time.time()
out("Re-review of TheoremF-p3-proof.md (p = 3). " + time.strftime('%Y-%m-%d %H:%M'))
out("=" * 100)

# ---------- Lemma A ----------
out("\n== Lemma A: lambda_M(D g) = -M lambda_M((psi - c) g) for random g; lambda_M(psi - c) = 0 ==")
random.seed(3)
allok = True; cnt = 0
for (a, b) in [(2,-1),(-1,-3),(4,4),(0,2),(-3,5),(1,-1)]:
    for c in (1, 2, 3):
        for M in (1, 2, 3, 4, 6, 9):
            cM = c*M; gam = phi_coeffs(a, b, M, cM)
            psi_c = psi_series(a, b, cM); psi_c[0] = Fr(-c)
            for trial in range(3):
                g = [Fr(random.randint(-7, 7), random.randint(1, 5)) for _ in range(cM+1)]
                Dg = [t*g[t] for t in range(cM+1)]
                lhs = lam(gam, Dg, cM); rhs = -M*lam(gam, smul(psi_c, g, cM), cM)
                cnt += 1
                if lhs != rhs: allok = False
            if lam(gam, psi_c, cM) != 0: allok = False
check(f"Lemma A exact in {cnt} random instances (6 pairs x c<=3 x M in {{1,2,3,4,6,9}}), and lambda_M(psi-c)=0", allok)

# ---------- Lemma B ----------
out("\n== Lemma B: A(N) - A(M) = sum_{j=2}^{3cM} (N^j/j!) lambda_M(C(L^j)) exactly; C(L) = 0; lambda_M(C(L^j)) in Z_(3) ==")
for (a, b, c, M) in [(2,-1,1,1),(2,-1,1,3),(3,-1,2,2),(-1,-3,1,3),(1,-1,2,2),(-2,5,3,2),(4,4,1,6),(0,-2,1,9)]:
    N = 3*M; K = 3*c*M; cM = c*M
    L = L_series(a, b, K); gam = phi_coeffs(a, b, M, cM)
    Lj = [Fr(1)] + [Fr(0)]*K; total = Fr(0); integral = True
    CL1 = cartier(L, cM)
    for j in range(1, K+1):
        Lj = smul(Lj, L, K)
        lj = lam(gam, cartier(Lj, cM), cM)
        if vp(lj) < 0: integral = False
        if j >= 2: total += Fr(N**j, factorial(j)) * lj
    lhs = Acoef(a, b, c, N) - Acoef(a, b, c, M)
    check(f"Lemma B (a,b,c,M)=({a},{b},{c},{M}): expansion exact, C(L)=0, integrality", Fr(lhs) == total and all(v == 0 for v in CL1) and integral, f"A(N)-A(M)={lhs}")

# ---------- Lemma C ----------
out("\n== Lemma C: v_3(N^2/2) = 2r, v_3(N^3/6) = 3r-1, v_3(N^j/j!) >= 3r (j >= 4); v_3(j!) = (j - s_3(j))/2 ==")
def s3(j):
    s = 0
    while j: s += j % 3; j //= 3
    return s
ok = True; worst = INF
for r in range(1, 8):
    for m in (1, 2, 4):
        N = m*3**r
        if vp(Fr(N**2, 2)) != 2*r or vp(Fr(N**3, 6)) != 3*r-1: ok = False
        for j in range(4, 250):
            sl = vp(Fr(N**j, factorial(j))) - 3*r; worst = min(worst, sl)
            if sl < 0: ok = False
ok2 = all(vp_fact(j) == (j - s3(j))//2 and (j - s3(j)) % 2 == 0 for j in range(1, 2000))
check(f"Lemma C for r <= 7, j < 250 (min slack at j >= 4: {worst}); digit-sum formula for j < 2000", ok and ok2 and worst == 0)

# ---------- Lemma D ----------
out("\n== Lemma D: (N^3/6) lambda_M(C(L^3)) ≡ (9M^3/2) lambda_M(L) (mod 3^{3r}); C(L^3) ≡ L(y) (mod 3) ==")
for (a, b) in [(2,-1),(-1,-3),(1,-1),(3,3),(-2,5),(0,4)]:
    row = []; ok = True
    K0 = 120
    L = L_series(a, b, K0); L3 = smul(smul(L, L, K0), L, K0)
    CL3 = cartier(L3, K0//3)
    if not all(vp(CL3[t] - L[t]) >= 1 for t in range(K0//3 + 1)): ok = False
    for c in (1, 2, 3):
        for (r, m) in [(1,1),(1,2),(2,1),(2,2),(3,1)]:
            M = m*3**(r-1); N = 3*M; cM = c*M; K = 3*cM
            if K > 300: continue
            L = L_series(a, b, K); L3 = smul(smul(L, L, K), L, K)
            gam = phi_coeffs(a, b, M, cM)
            diff = Fr(N**3, 6)*lam(gam, cartier(L3, cM), cM) - Fr(9*M**3, 2)*lam(gam, L, cM)
            sl = vp(diff) - 3*r; row.append(f"c{c}r{r}m{m}:{fmt(sl)}")
            if sl < 0: ok = False
    check(f"Lemma D (a,b)=({a},{b}): C(L^3)≡L mod 3 to y^40; congruence slack", ok, " ".join(row))

# ---------- Lemma E ----------
out("\n== Lemma E: (a) S_2 ≡ -3^{e-1} (mod 3^e); (b) 2S_1 ≡ 3^{2e-1} (mod 3^{2e}); (c) S_2^± ≡ 0 (mod 3^e).  exact leading digits ==")
for e in range(1, 7):
    R = [u for u in range(1, 3**e) if u % 3]
    S1 = sum(Fr(1, u) for u in R); S2 = sum(Fr(1, u*u) for u in R); S2pm = sum(Fr((-1)**(u+1), u*u) for u in R); S1pm = sum(Fr((-1)**(u+1), u) for u in R)
    ca = vp(S2 + 3**(e-1)) >= e; cb = vp(2*S1 - 3**(2*e-1)) >= 2*e; cc = vp(S2pm) >= e
    check(f"Lemma E e={e}: (a) {ca} [v_3(S_2)={vp(S2)}], (b) {cb} [v_3(S_1)={vp(S1)}], (c) {cc} [v_3(S_2^±)={vp(S2pm)}]; v_3(S_1^±)={vp(S1pm)}", ca and cb and cc)

# ---------- Lemma F ----------
out("\n== Lemma F: T = l 3^e, 3 ∤ l: (a) H_T ≡ -3^{2e-1} (mod 3^{2e}), v_3(H_T) = 2e-1; (b) T even: H_T^± ≡ 0 (mod 3^{2e}) ==")
bad_a = []; bad_b = []; cnt_a = cnt_b = 0; by_e = {}
for T in range(3, TMAX+1, 3):
    e = vp(T); l = T // 3**e
    cnt_a += 1
    if not (vp(Hs[T] + 3**(2*e-1)) >= 2*e and vp(Hs[T]) == 2*e-1): bad_a.append(T)
    if T % 2 == 0:
        cnt_b += 1; sl = vp(Hp[T]) - 2*e; by_e[e] = min(by_e.get(e, INF), sl)
        if sl < 0: bad_b.append(T)
check(f"Lemma F(a) for all T ≡ 0 (mod 3), T <= {TMAX} ({cnt_a} values, e up to {vp(3**7)})", not bad_a, f"bad T: {bad_a[:8]}")
check(f"Lemma F(b) for all even T ≡ 0 (mod 3), T <= {TMAX} ({cnt_b} values); min slack by e: {by_e}", not bad_b, f"bad T: {bad_b[:8]}")
odd_min = min(vp(Hp[T]) - 2*vp(T) for T in range(3, TMAX+1, 6))
out(f"       (for odd T the bound fails: min v_3(H_T^±) - 2e over odd T = {odd_min})")

# ---------- Lemma G at p = 3 ----------
out("\n== Lemma G at p = 3 (direct convolution vs the harmonic formulas), T <= 300 ==")
K = 300
U = [Fr(0)] + [Fr(1, j) if j % 3 else Fr(0) for j in range(1, K+1)]
V = [Fr(0)] + [Fr((-1)**(j+1), j) if j % 3 else Fr(0) for j in range(1, K+1)]
U2 = smul(U, U, K); V2 = smul(V, V, K); UV = smul(U, V, K)
check("Lemma G at p=3, all T = 3, 6, ..., 300", all(U2[T] == coefU2(T) and V2[T] == coefV2(T) and UV[T] == coefUV(T) for T in range(3, K+1, 3)))

# ---------- Lemma H ----------
out("\n== Lemma H: g_t = [x^{3t}] L^2 / t in Z_(3), g_t ≡ a^2 (-1)^t + b^2 (mod 3), t <= 400 (direct convolution, no Lemma G) ==")
TT = 400
U2d = {}; V2d = {}; UVd = {}
for t in range(1, TT+1):
    T = 3*t
    U2d[t] = sum(Fr(1, i*(T-i)) for i in range(1, T) if i % 3 and (T-i) % 3)
    V2d[t] = sum(Fr((-1)**(T+2), i*(T-i)) for i in range(1, T) if i % 3 and (T-i) % 3)
    UVd[t] = sum(Fr((-1)**(T-i+1), i*(T-i)) for i in range(1, T) if i % 3 and (T-i) % 3)
for (a, b) in [(2,-1),(3,-1),(4,-1),(-1,-3),(1,-1),(0,1),(1,0),(2,2),(3,3),(-3,0),(6,-9),(5,7),(-4,2),(1,2)]:
    ok_int = True; ok_res = True; bad = []
    for t in range(1, TT+1):
        gt = (a*a*V2d[t] - 2*a*b*UVd[t] + b*b*U2d[t]) / t
        if vp(gt) < 0: ok_int = False; bad.append(t)
        elif mod3(gt) != (a*a*(-1)**t + b*b) % 3: ok_res = False; bad.append(t)
    check(f"Lemma H (a,b)=({a},{b}): integral {ok_int}, residue a^2(-1)^t+b^2 {ok_res} for t<=400 (incl. t=3,9,27,81,243)", ok_int and ok_res, f"bad t: {bad[:6]}")
# the three ingredients separately, including t divisible by 3
ok = all(mod3(U2d[t]/t) == 1 and mod3(V2d[t]/t) == (-1)**t % 3 and (t % 2 == 1 or mod3(UVd[t]/t) == 0) and (t % 2 == 0 or UVd[t] == 0) for t in range(1, TT+1))
check("Lemma H ingredients: [x^T]U^2/t ≡ 1, [x^T]V^2/t ≡ (-1)^t, [x^T]UV/t ≡ 0 (mod 3) (UV = 0 for odd t), t <= 400", ok)
# closed form of gbar
ok = True
for (a, b) in [(2,-1),(0,1),(1,0),(1,1),(1,2),(2,2),(0,2),(5,7)]:
    gb = [0] + [(a*a*(-1)**t + b*b) % 3 for t in range(1, 61)]
    # gbar * (1-y^2) should equal y[(b^2-a^2) + (a^2+b^2) y]
    prod = [(gb[t] - (gb[t-2] if t >= 2 else 0)) % 3 for t in range(61)]
    target = [0, (b*b - a*a) % 3, (a*a + b*b) % 3] + [0]*58
    if prod != target: ok = False
check("Lemma H(b) closed form gbar = y[(b^2-a^2) + (a^2+b^2)y]/(1-y^2) in F_3[[y]]", ok)

# ---------- Lemma J ----------
out("\n== Lemma J over F_3 (series to order 150; rational-function identities with denominators (1-y^2)^2 are decided by this): ==")
KJ = 150
def f3mul(f, g):
    h = [0]*(KJ+1)
    for i, x in enumerate(f[:KJ+1]):
        if x == 0: continue
        for j, y in enumerate(g[:KJ+1-i]):
            if y: h[i+j] = (h[i+j] + x*y) % 3
    return h
def f3inv_1my2sq():
    # 1/(1-y^2)^2 = sum (k+1) y^{2k}
    s = [0]*(KJ+1)
    for k in range(0, KJ//2+1): s[2*k] = (k+1) % 3
    return s
classes_ii = lambda a, b, c: (c % 3 == 0) or ((a+b-c) % 3 == 0) or (a % 3 == 0 and b % 3 == 0)
J_ok = True; table = []; R1_noconst_ok = True; R1_allconst_ok = True; R1_bad = []
for a in range(3):
    for b in range(3):
        Lbar = [0] + [((ell(a, b, i) % 3) * pow(i, -1, 3)) % 3 if i % 3 else 0 for i in range(1, KJ+1)]
        psibar = [0] + [ell(a, b, i) % 3 for i in range(1, KJ+1)]
        gbar = [0] + [(a*a*(-1)**t + b*b) % 3 for t in range(1, KJ+1)]
        Dpsibar = [(i*psibar[i]) % 3 for i in range(KJ+1)]
        alpha = (a - b) % 3; beta = (-(a+b)) % 3
        # (a)
        ratA = f3mul([0, alpha, (2*beta) % 3, alpha] + [0]*(KJ-3), f3inv_1my2sq())
        if Lbar != Dpsibar or Lbar != ratA: J_ok = False; table.append(f"(a) fails at (a,b)=({a},{b})")
        for c in range(3):
            psimc = psibar[:]; psimc[0] = (-c) % 3
            consts = [Kc for Kc in range(3) if Lbar == f3mul(psimc, [(gbar[0] + Kc) % 3] + gbar[1:])]
            # what the LEMMA asserts (used in the proof of (ii)):
            if c % 3 and (a+b-c) % 3 == 0: need = 0            # J(b): K0 = 0
            elif c % 3 == 0 and (a-b) % 3: need = 1            # J(c): K0 = 1
            elif c % 3 == 0 and a % 3: need = 2                # J(c): K0 = 2
            elif a % 3 == 0 and b % 3 == 0: need = 0           # proof of (ii), third case: K0 := 0 (Lbar = psibar = gbar = 0)
            else: need = None
            table.append(f"(a,b,c)≡({a},{b},{c}): constants K with Lbar=(psibar-c)(gbar+K): {consts}; lemma needs K0={need}; in class (ii): {classes_ii(a,b,c)}")
            if need is not None and need not in consts: J_ok = False
            # Remark 1 parenthetical: outside (ii) no constant works; 'for a ≡ b ≡ 0 every constant works because both sides vanish'
            if not classes_ii(a, b, c) and consts: R1_noconst_ok = False
            if a % 3 == 0 and b % 3 == 0 and consts != [0, 1, 2]: R1_allconst_ok = False; R1_bad.append(((a, b, c), consts))
for s in table: out("   " + s)
check("Lemma J (a),(b),(c) [+ K0 := 0 for a≡b≡0] hold in F_3[[y]] for all 27 residue classes", J_ok)
check("Remark 1: outside the classes of (ii) NO constant K has Lbar = (psibar-c)(gbar+K)", R1_noconst_ok)
check("Remark 1 parenthetical: 'for a ≡ b ≡ 0 every constant works because both sides vanish'", R1_allconst_ok, f"classes where only some constants work: {R1_bad} (for 3 ∤ c the right side is (psibar - c)K = -cK, which vanishes only for K = 0)")
# (b) stated polynomial identity and (c) stated polynomial identity, directly in F_3[y]
okb = okc = True
for a in range(3):
    for b in range(3):
        alpha = (a-b) % 3; beta = (-(a+b)) % 3
        for c in (1, 2):
            if (a+b-c) % 3: continue
            lhs = [(-c*(b*b-a*a)) % 3, (alpha*(b*b-a*a) - c*(a*a+b*b)) % 3, (alpha*(a*a+b*b)) % 3]
            if lhs != [alpha % 3, c % 3, alpha % 3]: okb = False
        K0 = 1 if (a-b) % 3 else (2 if a % 3 else 0)
        q = [K0 % 3, (b*b-a*a) % 3, (a*a+b*b-K0) % 3]
        prod = [0]*4
        for i, x in enumerate([alpha, beta]):
            for j, y in enumerate(q): prod[i+j] = (prod[i+j] + x*y) % 3
        if prod != [alpha, (2*beta) % 3, alpha, 0]: okc = False
check("Lemma J(b) polynomial identity (alpha y - c)[(b^2-a^2)+(a^2+b^2)y] = alpha + c y + alpha y^2 in all cases a+b≡c≢0", okb)
check("Lemma J(c) polynomial identity (alpha+beta y)[K0 + (b^2-a^2)y + (a^2+b^2-K0)y^2] = alpha + 2 beta y + alpha y^2 for 3|c", okc)

# ---------- Proposition I ----------
out("\n== Proposition I: A(3M) - A(M) ≡ (9M^3/2) lambda_M(L - (psi-c) g) (mod 3^{3r}); and Remark 1 digit formula ==")
def propI(a, b, c, r, m):
    M = m*3**(r-1); N = 3*M; cM = c*M
    g = [Fr(0)] + [direct_L2_coef(a, b, 3*t)/t for t in range(1, cM+1)]
    L = L_series(a, b, cM); psi_c = psi_series(a, b, cM); psi_c[0] = Fr(-c)
    f = smul(psi_c, g, cM); f = [L[t] - f[t] for t in range(cM+1)]
    gam = phi_coeffs(a, b, M, cM)
    lamv = lam(gam, f, cM)
    AN = Acoef(a, b, c, N); AM = gam[cM]
    diff = AN - AM - Fr(9*M**3, 2)*lamv
    digit_ok = (vp(lamv) >= 0) and (mod3(Fr(AN - AM, 3**(3*r-1))) == (-m**3 * mod3(lamv)) % 3)
    return vp(diff) - 3*r, vp(AN - AM) - 3*r, digit_ok, mod3(lamv)
pairs = [(2,-1),(3,-1),(4,-1),(-1,-3),(1,-1),(0,2),(2,2),(1,2),(-4,3),(5,2),(3,3),(-3,1),(4,4),(-2,-5),(6,-3),(-7,1)]
nfail = 0; ntest = 0; weak = True; digits_all = True
for c in (1, 2, 3):
    for (a, b) in pairs:
        row = []
        for (r, ms) in ((1, (1, 2, 4, 5)), (2, (1, 2, 4)), (3, (1, 2)), (4, (1,))):
            for m in ms:
                if c*3**r*m > 500: continue
                sl, slA, dok, dig = propI(a, b, c, r, m); ntest += 1
                if sl < 0: nfail += 1
                if slA < -1: weak = False
                if not dok: digits_all = False
                row.append(f"r{r}m{m}:{fmt(sl)}/{fmt(slA)}/d{dig}")
        out(f"   (a,b,c)=({a},{b},{c}) cls(ii)={classes_ii(a,b,c)}: " + " ".join(row))
check(f"Proposition I exact mod 3^(3r) in {ntest} cases ({nfail} failures); weak bound 3^(3r-1) always; Remark 1 digit formula always", nfail == 0 and weak and digits_all)
out("   (format: slack of the congruence / slack of A(N)-A(M) vs 3r / digit = lambda_M(L-(psi-c)g) mod 3)")

# ---------- Theorem F_3 ----------
out("\n== Theorem F_3: slack = v_3(A(3M)-A(M)) - 3r, M = m 3^{r-1}, 3 ∤ m; r <= 4, m <= 8, cN <= 600 ==")
def classify(a, b, c):
    if c % 3 == 0: return 'good 3|c'
    if (a+b-c) % 3 == 0: return 'good a+b=c'
    if a % 3 == 0 and b % 3 == 0: return 'good a=b=0'
    return 'BAD'
tri = [(2,-1,1),(3,-1,2),(4,-1,3),(-1,-3,1),(1,-1,1),(1,-1,2),(-1,2,1),(5,2,1),(-4,0,2),(2,2,1),(-3,1,1),(1,-1,3),(5,-2,3),(-2,-1,3),
       (3,0,1),(0,3,2),(-3,-3,1),(6,-3,2),(-6,3,1),(3,-6,2),(9,0,1),
       (1,2,1),(4,4,1),(5,2,2),(2,-1,2),(3,-1,1),(-3,-2,2),(-2,-3,2),(3,4,2),(4,3,2),(-5,-1,1),(7,-3,1),(-2,5,3),(0,-4,2),(-1,5,1),(3,2,4)]
min_by_class = {}
for (a, b, c) in tri:
    cls = classify(a, b, c); row = []; worst = INF
    for r in (1, 2, 3, 4):
        for m in (1, 2, 4, 5, 7, 8):
            M = m*3**(r-1); N = 3*M
            if c*N > 600: continue
            sl = vp(Acoef(a, b, c, N) - Acoef(a, b, c, M)) - 3*r
            worst = min(worst, sl); row.append(f"r{r}m{m}:{fmt(sl)}")
    min_by_class[cls] = min(min_by_class.get(cls, INF), worst)
    need = -1 if cls == 'BAD' else 0
    check(f"F_3 ({a},{b},{c}) [{cls}] min slack {fmt(worst)} (need >= {need})", worst >= need, " ".join(row))
out(f"   min slack by class: {min_by_class}")

# ---------- Remark 1: A352373 digits ----------
out("\n== Remark 1 sentence: 'the data show the digit is nonzero for suitable m ..., e.g. for A352373 at every tested (r, m)' ==")
row = []; zero_digit = []
for r in (1, 2, 3):
    for m in (1, 2, 4, 5, 7, 8):
        M = m*3**(r-1); N = 3*M
        if N > 200: continue
        d = Acoef(-1, -3, 1, N) - Acoef(-1, -3, 1, M)
        digit = (d // 3**(3*r-1)) % 3 if vp(d) >= 3*r-1 else None
        row.append(f"r{r}m{m}:v3={vp(d)} (3r-1={3*r-1}) digit={digit}")
        if digit == 0: zero_digit.append((r, m))
out("   A352373 = A_(-1,-3,1): " + "; ".join(row))
check("Remark 1 claim 'A352373 digit nonzero at every tested (r,m)' (tested (r,m) in the note's own V1: m in {1,2})", not any(m <= 2 for (r, m) in zero_digit), f"(r,m) with ZERO digit: {zero_digit}")

# ---------- Remark 3: sweep survivors ----------
out("\n== Remark 3 / Observation: triples outside (ii) that pass the sweep range (m in {1,2,4}, r<=3) -- do they fail for larger m? ==")
for (a, b, c) in [(-3,-2,2),(-2,-3,2),(3,4,2),(4,3,2)]:
    row = []; fails = []
    for m in range(1, 30):
        if m % 3 == 0: continue
        d = Acoef(a, b, c, 3*m) - Acoef(a, b, c, m); sl = vp(d) - 3
        row.append(f"m{m}:{fmt(sl)}")
        if sl < 0: fails.append(m)
    check(f"({a},{b},{c}) [class ({a%3},{b%3},{c%3}), outside (ii)] r=1: fails (slack -1) at some m < 30: {fails}", len(fails) > 0, " ".join(row))
# Observation: every residue class outside (ii) (c in {1,2}) contains a sweep member (-4<=a,b<=5) with slack -1 for some r<=3, m in {1,2,4}
out("   Observation check over the sweep range (-4<=a,b<=5, c in {1,2}, r<=3, m in {1,2,4}):")
cls_fail = {}; cls_members = {}
for c in (1, 2):
    for a in range(-4, 6):
        for b in range(-4, 6):
            if (a, b) == (0, 0): continue
            key = (a % 3, b % 3, c)
            if classes_ii(a, b, c): continue
            mn = INF
            for r in (1, 2, 3):
                for m in (1, 2, 4):
                    N = m*3**r; M = m*3**(r-1)
                    if c*N > 330: continue
                    mn = min(mn, vp(Acoef(a, b, c, N) - Acoef(a, b, c, M)) - 3*r)
            cls_members.setdefault(key, []).append(((a, b), fmt(mn)))
            if mn < 0: cls_fail[key] = cls_fail.get(key, 0) + 1
allcls = sorted(cls_members)
for key in allcls:
    out(f"     class {key}: {len(cls_members[key])} members, {cls_fail.get(key,0)} with slack -1; holders: {[m for m in cls_members[key] if m[1] != '-1']}")
check("Observation: every residue class outside (ii) with c in {1,2} has a sweep member with slack -1", all(cls_fail.get(k, 0) > 0 for k in allcls))

out("\n" + "=" * 100)
out(f"SUMMARY: {NPASS} passed, {NFAIL} failed; elapsed {time.time()-t0:.1f}s")
open(OUT, 'w').write("\n".join(LINES) + "\n")
