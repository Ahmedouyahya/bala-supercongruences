#!/usr/bin/env python3
# Independent re-review of notes/TheoremF-coefficient-framing-proof.md (p >= 5 note): CONGRUENCES AND VALUATION BOUNDS.
#   Lemma 2 (S_1, S_2), Lemma 3 (H_T, H_T^±), Lemma 6 (v_p(gamma_s)), the estimate (2) for eps_T,
#   the j >= 3 factorial bound, Theorem F itself with slack (r up to 3, p = 5, 7, 11, 13, negative a, b, c = 1),
#   and a term-by-term check of (1) at p = 5, r = 2, 3 (the Lemma-6 branch tau <= r-2).
# Output: numerics/out/rereview_theoremF_p5_valuations.txt
import os, sys, time
from fractions import Fraction as Fr
from math import comb, factorial

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repository root
OUT = os.path.join(ROOT, 'numerics/out/rereview_theoremF_p5_valuations.txt')
LINES = []
def out(s=''):
    print(s); LINES.append(s)
NPASS = NFAIL = 0
def check(name, ok, detail=''):
    global NPASS, NFAIL
    if ok: NPASS += 1
    else: NFAIL += 1
    out(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ''))

INF = 10**6
def vp(x, p):
    x = Fr(x)
    if x == 0: return INF
    a, b = x.numerator, x.denominator; v = 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
def vp_fact(j, p):
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
def sexp(f, K):
    g = [Fr(0)]*(K+1); g[0] = Fr(1)
    for n in range(1, K+1):
        g[n] = sum(k*f[k]*g[n-k] for k in range(1, n+1)) / n
    return g
def L_series(a, b, p, K):
    return [Fr(0)] + [Fr(a*(-1)**(i+1) - b, i) if i % p else Fr(0) for i in range(1, K+1)]
def fmt(v): return 'inf' if v >= INF//2 else f"{v:+d}"

t0 = time.time()
out("Re-review of TheoremF-coefficient-framing-proof.md: congruences and valuations. " + time.strftime('%Y-%m-%d %H:%M'))
out("=" * 100)

# ---------- Lemma 2 ----------
out("\n== Lemma 2: S_2 ≡ 0 (mod p^e), S_1 ≡ 0 (mod p^{2e}) for p >= 5; and the section-6 remark at p = 3 (v_3(S_2) = e-1, v_3(S_1) = 2e-1) ==")
for p in (5, 7, 11, 13):
    for e in range(1, (5 if p == 5 else 4 if p == 7 else 3)):
        R = [u for u in range(1, p**e) if u % p]
        S1 = sum(Fr(1, u) for u in R); S2 = sum(Fr(1, u*u) for u in R)
        check(f"Lemma 2 p={p} e={e}: v_p(S_2)={vp(S2,p)} (need >= {e}), v_p(S_1)={vp(S1,p)} (need >= {2*e})", vp(S2, p) >= e and vp(S1, p) >= 2*e)
for e in range(1, 7):
    R = [u for u in range(1, 3**e) if u % 3]
    S1 = sum(Fr(1, u) for u in R); S2 = sum(Fr(1, u*u) for u in R)
    check(f"p=3 remark e={e}: v_3(S_2)={vp(S2,3)} == e-1, v_3(S_1)={vp(S1,3)} == 2e-1", vp(S2, 3) == e-1 and vp(S1, 3) == 2*e-1)

# ---------- Lemma 3 ----------
out("\n== Lemma 3: e = v_p(T) >= 1: (i) H_T ≡ 0 (mod p^{2e}); (ii) T even: H_T^± ≡ 0 (mod p^{2e}).  slack = v_p(.) - 2e ==")
for p in (5, 7, 11, 13):
    Tmax = {5: 1000, 7: 700, 11: 605, 13: 507}[p]
    H = Fr(0); Hpm = Fr(0)
    worst = {}; worstpm = {}; odd_pm_min = INF
    for i in range(1, Tmax+1):
        T = i
        if T % p == 0:
            e = vp(T, p)
            worst[e] = min(worst.get(e, INF), vp(H, p) - 2*e)
            if T % 2 == 0: worstpm[e] = min(worstpm.get(e, INF), vp(Hpm, p) - 2*e)
            else: odd_pm_min = min(odd_pm_min, vp(Hpm, p))
        if i % p:
            H += Fr(1, i); Hpm += Fr((-1)**(i+1), i)
    check(f"Lemma 3(i) p={p}, T <= {Tmax}: min slack by e = {worst}", min(worst.values()) >= 0)
    check(f"Lemma 3(ii) p={p}, even T <= {Tmax}: min slack by e = {worstpm}", min(worstpm.values()) >= 0)
    out(f"       (for odd T, min v_p(H_T^±) = {odd_pm_min}: the parity hypothesis in (ii) is needed)")

# ---------- Lemma 6 ----------
out("\n== Lemma 6: M = p^{r-1} m, p ∤ m; s >= 1, sigma = v_p(s) <= r-2  =>  v_p(gamma_s) >= r-1-sigma.  slack = v_p(gamma_s) - (r-1-sigma) ==")
for p in (5, 7):
    for r in (2, 3, 4):
        for m in (1, 2, 3):
            M = m*p**(r-1)
            if M > 250 or m % p == 0: continue
            K = 3*M
            worst_all = INF; detail = []
            for (a, b) in [(3,-1),(4,-1),(-1,-3),(2,-2),(1,1),(-2,5),(-3,-4),(5,7),(1,0),(0,-1)]:
                gam = phi_coeffs(a, b, M, K)
                worst = INF
                for s in range(1, K+1):
                    if gam[s] == 0: continue
                    sig = vp(s, p)
                    if sig <= r-2: worst = min(worst, vp(gam[s], p) - (r-1-sig))
                detail.append(f"({a},{b}):{fmt(worst)}")
                worst_all = min(worst_all, worst)
            check(f"Lemma 6 p={p} r={r} m={m} (M={M}), 10 pairs: min slack {fmt(worst_all)}", worst_all >= 0, " ".join(detail))

# ---------- factorial bound ----------
out("\n== j >= 3 bound (p >= 5): v_p(N^j/j!) >= 3r;  chain v_p(j!) <= (j-1)/(p-1) <= (j-1)/4 <= (j-3) r (j >= 4) ==")
for p in (5, 7, 11):
    ok = True; worst = INF
    for r in range(1, 8):
        for j in range(3, 300):
            sl = j*r - vp_fact(j, p) - 3*r
            worst = min(worst, sl)
            if sl < 0: ok = False
            if j >= 4 and not (vp_fact(j, p) <= Fr(j-1, p-1) <= Fr(j-1, 4) <= (j-3)*r): ok = False
    check(f"p={p}: v_p(N^j/j!) >= 3r for 3 <= j < 300, 1 <= r <= 7 (min slack {worst}); chain inequality holds", ok)
out("   (Lemma C of the p=3 note) p=3: v_3(N^2/2)=2r, v_3(N^3/6)=3r-1, v_3(N^j/j!)>=3r for j>=4:")
ok = True; worst4 = INF
for r in range(1, 8):
    if 2*r - vp_fact(2, 3) != 2*r or 3*r - vp_fact(3, 3) != 3*r - 1: ok = False
    for j in range(4, 300):
        sl = j*r - vp_fact(j, 3) - 3*r; worst4 = min(worst4, sl)
        if sl < 0: ok = False
        if not (vp_fact(j, 3) == Fr(j - sum(int(d) for d in __import__('numpy').base_repr(j, 3)), 2) if False else True): pass
check(f"Lemma C: all three claims for r <= 7, j < 300 (min slack at j>=4: {worst4}, attained at j=4, r=1)", ok and worst4 == 0)

# ---------- estimate (2) ----------
out("\n== Estimate (2): v_p(eps_T) >= min(2r + v_p(T), 3r) for T ≡ 0 (mod p), eps_T = [x^T](exp(NL) - 1), N = m p^r ==")
for p in (5, 7):
    for r in (1, 2, 3):
        for m in (1, 2):
            N = m*p**r
            if N > 250: continue
            Tmax = 250 if p == 5 else 196
            worst_all = INF; detail = []
            for (a, b) in [(2,-1),(-1,-3),(3,-1),(1,1),(-2,5),(4,-1)]:
                E = sexp([N*x for x in L_series(a, b, p, Tmax)], Tmax)
                worst = INF; where = None
                for T in range(p, Tmax+1, p):
                    bound = min(2*r + vp(T, p), 3*r)
                    sl = vp(E[T], p) - bound
                    if sl < worst: worst, where = sl, T
                detail.append(f"({a},{b}):{fmt(worst)}@T={where}")
                worst_all = min(worst_all, worst)
            check(f"(2) p={p} r={r} m={m} (N={N}), T <= {Tmax}: min slack {fmt(worst_all)}", worst_all >= 0, " ".join(detail))

# ---------- Theorem F ----------
out("\n== Theorem F: slack = v_p(A(n p^r) - A(n p^{r-1})) - 3r  (need >= 0); p ∤ n; cN <= 600 ==")
triples = [(3,-1,2),(4,-1,3),(2,-1,1),(-1,-3,1),(1,-1,2),(1,-1,1),(2,0,1),(5,-2,2),(-3,2,1),(-2,-5,1),(-4,3,2),(7,-4,3),(1,1,1),(0,-3,1),(-1,-1,1),(6,-6,1),(-5,-1,1),(3,2,4)]
global_min = INF
for p in (5, 7, 11, 13):
    for (a, b, c) in triples:
        row = []; worst = INF
        for r in (1, 2, 3):
            for n in (1, 2, 3, 4):
                N = n*p**r
                if c*N > 600 or n % p == 0: continue
                d = Acoef(a, b, c, N) - Acoef(a, b, c, N//p)
                sl = vp(d, p) - 3*r
                worst = min(worst, sl); row.append(f"r{r}n{n}:{fmt(sl)}")
        global_min = min(global_min, worst)
        check(f"Theorem F p={p} (a,b,c)=({a},{b},{c}) min slack {fmt(worst)}", worst >= 0, " ".join(row))
out(f"   global min slack over all Theorem F tests: {fmt(global_min)}")

# ---------- term-by-term check of (1) ----------
out("\n== Term-by-term check of (1) at p = 5: each term gamma_s * eps_{p(cM-s)} has v_p >= 3r; branch bookkeeping of section 4 ==")
p = 5
for (a, b, c) in [(2,-1,1),(3,-1,2),(-1,-3,1),(-2,5,1)]:
    for (r, m) in [(1, 1), (2, 1), (2, 2), (3, 1), (3, 2)]:
        M = m*p**(r-1); N = p*M; K = p*c*M
        if K > 250: continue
        E = sexp([N*x for x in L_series(a, b, p, K)], K)
        gam = phi_coeffs(a, b, M, c*M)
        worst = INF; n_branchA = n_branchB = 0; branch_ok = True; worst_s = None
        for s in range(0, c*M):
            T = p*(c*M - s); tau = vp(c*M - s, p)
            term = gam[s]*E[T]
            v = vp(term, p)
            if v - 3*r < worst: worst, worst_s = v - 3*r, s
            if tau >= r-1:
                n_branchA += 1
                if vp(E[T], p) < 3*r: branch_ok = False
            else:
                n_branchB += 1
                if not (vp(s, p) == tau and (gam[s] == 0 or vp(gam[s], p) >= r-1-tau) and vp(E[T], p) >= 2*r+1+tau): branch_ok = False
        total = sum(gam[s]*E[p*(c*M-s)] for s in range(c*M))
        check(f"(1) termwise p=5 (a,b,c)=({a},{b},{c}) r={r} m={m}: min term slack {fmt(worst)} (at s={worst_s}); branches tau>=r-1: {n_branchA}, tau<=r-2: {n_branchB}; branch inequalities hold: {branch_ok}; total slack {fmt(vp(total,p)-3*r)}", worst >= 0 and branch_ok)

out("\n" + "=" * 100)
out(f"SUMMARY: {NPASS} passed, {NFAIL} failed; elapsed {time.time()-t0:.1f}s")
open(OUT, 'w').write("\n".join(LINES) + "\n")
