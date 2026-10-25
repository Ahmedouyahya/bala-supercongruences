# Independent re-review (2026-10-15) of notes/A376462-proof-first-congruence.md: sections 0-4 (first congruence) and
# the superseded section 5 (second congruence, r=1).  Exact arithmetic (Fraction / comb).  Includes r=3, p in {5,7,11}, p|m.
# Run: ~/venvs/general/bin/python -I numerics/rereview_oss_a376462.py > numerics/out/rereview_oss_a376462.txt
from math import comb
from fractions import Fraction
import time

INF = 10**9
def vp(x, p):
    x = Fraction(x)
    if x == 0: return INF
    a, b = x.numerator, x.denominator; v = 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
def C(a, b): return comb(a, b) if 0 <= b <= a else 0
def gbinom(a, k):
    if k < 0: return 0
    num = 1
    for i in range(k): num *= (a - i)
    den = 1
    for i in range(2, k + 1): den *= i
    return num // den
def sl(v, need): return "inf" if v >= INF else v - need

FAIL = 0; PASS = 0
def report(name, ok, detail=""):
    global FAIL, PASS
    if ok: PASS += 1
    else: FAIL += 1
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""))

def A108625(n, j): return sum(comb(n, i) ** 2 * comb(n + j - i, j - i) for i in range(j + 1))
def a_def(n): return sum(comb(n, k) ** 2 * comb(n + k, k) * A108625(n, n - k) for k in range(n + 1))
def T(n, k, i): return C(n, k) ** 2 * C(n + k, k) * C(n, i) ** 2 * C(2 * n - k - i, n)

class Level:
    """arrays for fast T(n;k,i) = c1[k]*c2[i]*c3[k+i]"""
    def __init__(self, n):
        self.n = n
        self.c1 = [C(n, k) ** 2 * C(n + k, k) for k in range(n + 1)]
        self.c2 = [C(n, i) ** 2 for i in range(n + 1)]
        self.c3 = [C(2 * n - j, n) for j in range(2 * n + 1)]
    def T(self, k, i):
        if not (0 <= k <= self.n and 0 <= i <= self.n): return 0
        return self.c1[k] * self.c2[i] * self.c3[k + i]
    def total(self):
        return sum(self.c1[k] * self.c2[i] * self.c3[k + i] for k in range(self.n + 1) for i in range(self.n + 1))

# ---------------------------------------------------------------------------------------------
print("== Statement: a(n) against OEIS A376462 data; (1) double-sum form; representations")
oeis = [1, 5, 109, 3317, 121501, 4954505, 216867925, 9981053045, 476860000285, 23451310381505, 1180189308268609, 60519806861966105]
report("OEIS data n=0..11", [a_def(n) for n in range(12)] == oeis)
report("(1) a(n) = sum_{k,i} T(n;k,i), n<=16", all(a_def(n) == Level(n).total() for n in range(17)))
report("(R1) A108625(n,n-k) = sum_j C(n,j)C(n+j,j)C(n-k,j), n<=13", all(A108625(n, n - k) == sum(comb(n, j) * comb(n + j, j) * comb(n - k, j) for j in range(n + 1)) for n in range(14) for k in range(n + 1)))
report("symmetric form a(n)=sum_{j,k} C(n,j)C(n-j,k)C(n,j)C(n+j,j)C(n,k)C(n+k,k), n<=13", all(a_def(n) == sum(comb(n, j) * comb(n - j, k) * comb(n, j) * comb(n + j, j) * comb(n, k) * comb(n + k, k) for j in range(n + 1) for k in range(n - j + 1)) for n in range(14)))
def St(N, k, j): return C(N - 1, k) ** 2 * C(N + k - 1, k) * C(N - 1, k + j) ** 2 * C(N + j - 1, j)
report("(sec.5) a(N-1) = sum_{k+j<=N-1} S~(N;k,j), N<=20", all(a_def(N - 1) == sum(St(N, k, j) for k in range(N) for j in range(N - k)) for N in range(1, 21)))
# dual kernel remark
def Sstar(n, k, j): return gbinom(n + k, k) ** 2 * gbinom(n, k) * gbinom(n + k + j, k + j) ** 2 * gbinom(n, j)
dual_id = all(Sstar(-N, k, j) == (-1) ** (k + j) * St(N, k, j) for N in range(1, 9) for k in range(N) for j in range(N - k))
dual_seq = [sum(Sstar(-N, k, j) for k in range(N) for j in range(N - k)) for N in range(1, 6)]
report("(sec.5 remark) S*(-N;k,j) = (-1)^{k+j} S~(N;k,j) and sum = 1,-3,-11,1077,...", dual_id and dual_seq[:4] == [1, -3, -11, 1077], f"sums N=1..5: {dual_seq}")
# Laurent constant term
from collections import defaultdict
def pmul(P, Q):
    R = defaultdict(int)
    for e1, c1 in P.items():
        for e2, c2 in Q.items():
            R[(e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2], e1[3] + e2[3])] += c1 * c2
    return R
one = {(0, 0, 0, 0): 1}; U = {(1, 0, 0, 0): 1}; V = {(0, 1, 0, 0): 1}; Z = {(0, 0, 1, 0): 1}; W = {(0, 0, 0, 1): 1}
def padd(*ps):
    R = defaultdict(int)
    for P in ps:
        for e, c in P.items(): R[e] += c
    return R
Lnum = pmul(pmul(pmul(pmul(padd(one, U, V), padd(one, Z)), padd(one, U, Z)), padd(one, W)), padd(one, V, W))
P = dict(one); ct = []
for n in range(0, 6):
    ct.append(P.get((n, n, n, n), 0)); P = pmul(P, Lnum)
report("a(n) = CT[Lambda^n], n<=5", ct == [a_def(n) for n in range(6)], str(ct))

# ---------------------------------------------------------------------------------------------
print("== Classes (S),(K),(I),(B) and the Theorem.  Slacks vs p^{3r} (B vs p^{4r}).")
GRID = [(5, 1, (1, 2, 3, 5, 10)), (5, 2, (1, 2, 3, 5)), (5, 3, (1, 2, 3, 5)), (7, 1, (1, 2, 3, 7, 14)), (7, 2, (1, 2, 3, 7)), (7, 3, (1, 2)),
        (11, 1, (1, 2, 3, 11)), (11, 2, (1, 2, 3, 11)), (11, 3, (1,))]
def Psi1(Mp, n1): return C(Mp - 1, n1) ** 2 * C(Mp + n1, n1) * sum(C(Mp, i1) ** 2 * C(2 * Mp - n1 - 1 - i1, Mp) for i1 in range(0, Mp + 1))
def Psi2(Mp, n1): return C(Mp - 1, n1) ** 2 * sum(C(Mp, k1) ** 2 * C(Mp + k1, k1) * C(2 * Mp - k1 - n1 - 1, Mp) for k1 in range(0, Mp + 1))
t0 = time.time()
for p, r, ms in GRID:
    for m in ms:
        N = m * p ** r; M = N // p
        if N > 1400: continue
        hi = Level(N); lo = Level(M)
        aN = hi.total(); aM = lo.total()
        # class S
        Ssum = 0; tw = INF; subbad = 0
        for Kp in range(M + 1):
            for Ip in range(M + 1):
                d = hi.T(p * Kp, p * Ip) - lo.T(Kp, Ip); Ssum += hi.T(p * Kp, p * Ip)
                if d: tw = min(tw, vp(d, p) - 3 * r)
                # sub-claims: valuation bound v_p(T(M;K',I')) >= 2 max(0,r-s) + 2 max(0,r-sigma) when nonzero
                if lo.T(Kp, Ip):
                    s = vp(p * Kp, p) if Kp else INF; sg = vp(p * Ip, p) if Ip else INF
                    need = 2 * max(0, r - s) + 2 * max(0, r - sg)
                    if vp(lo.T(Kp, Ip), p) < need: subbad += 1
                    # Q4 bound: C(p(2M-K'-I'),pM)/C(2M-K'-I',M) == 1 mod p^{3+v(2M-K'-I')+v(M)+v(M-K'-I')} when 0<M<2M-K'-I'
                    Aq = 2 * M - Kp - Ip
                    if 0 < M < Aq:
                        q4 = Fraction(C(p * Aq, p * M), C(Aq, M))
                        if vp(q4 - 1, p) < 3 + vp(Aq, p) + vp(M, p) + vp(Aq - M, p): subbad += 1
                        mu = min(s, sg)
                        if vp(q4 - 1, p) < r + 2 + 2 * min(r - 1, mu - 1): subbad += 1
                    if Kp:
                        q1 = Fraction(C(N, p * Kp), C(M, Kp)) if Kp <= M else None
                        if Kp < M and vp(q1 - 1, p) < r + s + min(r, s): subbad += 1
                        q2 = Fraction(C(N + p * Kp, p * Kp), C(M + Kp, Kp))
                        if vp(q2 - 1, p) < r + s + min(r, s): subbad += 1
        vS = vp(Ssum - aM, p) - 3 * r
        # class K and I, B
        Ksum = sum(hi.T(k, i) for k in range(1, N + 1) if k % p for i in range(0, N + 1, p))
        Isum = sum(hi.T(k, i) for k in range(0, N + 1, p) for i in range(1, N + 1) if i % p)
        Bsum = aN - Ssum - Ksum - Isum
        vK = vp(Ksum, p) - 3 * r; vI = vp(Isum, p) - 3 * r; vB = vp(Bsum, p) - 4 * r
        # S_K exact identity and reduction
        SK = sum(Fraction(C(N - 1, k - 1) ** 2 * C(N + k, k) * sum(C(N, i) ** 2 * C(2 * N - k - i, N) for i in range(0, N + 1, p)), k * k) for k in range(1, N + 1) if k % p)
        SI = sum(Fraction(C(N - 1, i - 1) ** 2 * sum(C(N, k) ** 2 * C(N + k, k) * C(2 * N - k - i, N) for k in range(0, N + 1, p)), i * i) for i in range(1, N + 1) if i % p)
        idK = (Ksum == N * N * SK); idI = (Isum == N * N * SI)
        sigK = []; sigI = []
        for s in range(1, r + 1):
            lvl = m * p ** (r - s); cK = {}; cI = {}; tK = Fraction(0); tI = Fraction(0)
            for k in range(1, N + 1):
                if k % p == 0: continue
                n1 = k // p ** s
                if n1 not in cK: cK[n1] = Psi1(lvl, n1); cI[n1] = Psi2(lvl, n1)
                tK += Fraction(cK[n1], k * k); tI += Fraction(cI[n1], k * k)
            sigK.append(tK); sigI.append(tI)
        redK = vp(SK - sigK[0], p) - r; redI = vp(SI - sigI[0], p) - r
        chK = [vp(sigK[i] - sigK[i + 1], p) - r for i in range(r - 1)]; chI = [vp(sigI[i] - sigI[i + 1], p) - r for i in range(r - 1)]
        endK = vp(sigK[-1], p) - r; endI = vp(sigI[-1], p) - r
        thm = vp(aN - aM, p) - 3 * r
        ok = (vS >= 0 and (tw >= 0) and subbad == 0 and vK >= 0 and vI >= 0 and vB >= 0 and idK and idI and redK >= 0 and redI >= 0
              and all(c >= 0 for c in chK + chI) and endK >= 0 and endI >= 0 and thm >= 0)
        def f(v): return "inf" if v >= INF else v
        report(f"classes p={p} r={r} m={m} N={N}", ok,
               f"S: sum slack {f(vS)}, termwise min {f(tw)}, subclaim failures {subbad} | K {f(vK)}, I {f(vI)}, B(vs 4r) {f(vB)} | K=N^2 S_K {idK}, I=N^2 S_I {idI} | S_K==Sig1 {f(redK)}, S_I==Sig1 {f(redI)} | chains K {chK} I {chI} | Sig_r: K {f(endK)} I {f(endI)} | THEOREM slack {thm}")
print(f"   (class block took {time.time()-t0:.1f}s)")

# ---------------------------------------------------------------------------------------------
print("== Lemma 7 (self-similarity) Psi_1, Psi_2: Psi(mp^t,n') == Psi(mp^{t-1},[n'/p]) mod p^t, all n' < 2mp^t+3; plus floor identities; plus Lemma 1 as used (C(N,pi') == C(M,i'))")
t0 = time.time()
for p in (5, 7, 11):
    for t in (1, 2, 3):
        for m in (1, 2, p):
            Mt = m * p ** t
            if Mt > 700: continue
            bad1 = bad2 = 0; tot = 0; w1 = w2 = INF
            for n1 in range(0, 2 * Mt + 3):
                tot += 1
                d1 = Psi1(Mt, n1) - Psi1(Mt // p, n1 // p); d2 = Psi2(Mt, n1) - Psi2(Mt // p, n1 // p)
                if d1 % p ** t: bad1 += 1
                if d2 % p ** t: bad2 += 1
                if d1: w1 = min(w1, vp(d1, p) - t)
                if d2: w2 = min(w2, vp(d2, p) - t)
            report(f"Lemma7 p={p} t={t} m={m} (M_t={Mt})", bad1 == 0 and bad2 == 0, f"{tot} cases; failures Psi1 {bad1}, Psi2 {bad2}; min slack Psi1 {w1 if w1<INF else 'all equal'}, Psi2 {w2 if w2<INF else 'all equal'}")
print(f"   (Lemma 7 block took {time.time()-t0:.1f}s)")
okf = True
for p in (5, 7, 11):
    for n1 in range(0, 200): okf &= (-(-(n1 + 1) // p) == n1 // p + 1)
    for M in (1, 2, 3, 7, 25):
        N = p * M
        for k in range(1, N + 1):
            if k % p == 0: continue
            for i1 in range(0, M + 1): okf &= ((2 * N - k - p * i1) // p == 2 * M - i1 - k // p - 1)
report("floor identities: ceil((n'+1)/p) = [n'/p]+1 and [(2N-k-pi')/p] = 2M-i'-[k/p]-1 (p∤k)", okf)
for p in (5, 7, 11):
    for r in (1, 2, 3):
        for m in (1, 2, p):
            N = m * p ** r; M = N // p
            if N > 4000: continue
            w = min((vp(C(N, p * i1) - C(M, i1), p) - r for i1 in range(0, M + 1) if C(N, p * i1) != C(M, i1)), default=INF)
            report(f"C(N,pi') == C(M,i') mod p^r, p={p} r={r} m={m}", w >= 0, f"min slack {w if w<INF else 'all equal'} (note: Lemma 1 actually gives >= r+2)")

# ---------------------------------------------------------------------------------------------
print("== SECTION 5 (SUPERSEDED): a(mp-1) == a(m-1) mod p^3 via S~; classes (S),(B),(K),(J) and the sub-claims")
def Hp(k, p): return sum(Fraction(1, i) for i in range(1, k + 1) if i % p)
for p in (5, 7, 11, 13):
    H1 = sum(Fraction(1, u) for u in range(1, p)); H2 = sum(Fraction(1, u * u) for u in range(1, p))
    s1 = sum(Fraction(1, u * v) for u in range(1, p) for v in range(1, p) if u + v < p); s2 = sum(Fraction(1, u * v) for u in range(1, p) for v in range(1, p) if u + v >= p)
    s3 = sum(Hp(u, p) / u for u in range(1, p))
    ids = (s1 == sum(Fraction(2, n) * Hp(n - 1, p) for n in range(2, p))) and (s1 == H1 * H1 - H2) and (s3 == (H1 * H1 + H2) / 2)
    report(f"sec5 harmonic facts p={p}", vp(H1, p) >= 2 and vp(H2, p) >= 1 and vp(s1, p) >= 1 and vp(s2, p) >= 1 and vp(s3, p) >= 1 and ids,
           f"v(H_{{p-1}})={vp(H1,p)} v(H2)={vp(H2,p)} v(sum_{{u+v<p}})={vp(s1,p)} v(sum_{{u+v>=p}})={vp(s2,p)} v(sum H_u/u)={vp(s3,p)} exact identities {ids}")
for p in (5, 7, 11, 13):
    for m in (1, 2, 3, 4, 5, 6, p, p + 1):
        N = m * p; M = m
        if N > 200: continue
        # classes
        S_pairs = [(k, j) for k in range(N) for j in range(N - k)]
        SS = sum(St(N, k, j) for k, j in S_pairs if k % p == 0 and j % p == 0)
        KU = sum(St(N, k, j) for k, j in S_pairs if k % p and j % p == 0)
        JU = sum(St(N, k, j) for k, j in S_pairs if k % p == 0 and j % p)
        BU = sum(St(N, k, j) for k, j in S_pairs if k % p and j % p)
        aM1 = sum(St(M, k, j) for k in range(M) for j in range(M - k))
        tot = vp(a_def(N - 1) - a_def(M - 1), p) - 3
        # (S) termwise and quotient rewriting
        tw = INF; qid = True
        for kp in range(M):
            for jp in range(M - kp):
                d = St(N, p * kp, p * jp) - St(M, kp, jp)
                if d: tw = min(tw, vp(d, p) - 3)
                qid &= Fraction(C(N - 1, p * kp), C(M - 1, kp)) == Fraction(C(p * M, p * kp), C(M, kp))
        # (B) Lucas claim: R(k,j) mod p depends only on ([k/p],[j/p],delta); and completed block formula
        def R(k, j): return C(N - 1, k) ** 2 * C(N + k - 1, k - 1) * C(N - 1, k + j) ** 2 * C(N + j - 1, j - 1)
        def Rlucas(n1, n2, dl): return C(m - 1, n1) ** 2 * C(m + n1, n1) * C(m - 1, n1 + n2 + dl) ** 2 * C(m + n2, n2)
        lucas_ok = True
        for k in range(1, N):
            if k % p == 0: continue
            for j in range(1, N):
                if j % p == 0: continue
                dl = 1 if (k % p + j % p) >= p else 0
                lucas_ok &= ((R(k, j) - Rlucas(k // p, j // p, dl)) % p == 0)
        s1 = sum(Fraction(1, u * v) for u in range(1, p) for v in range(1, p) if u + v < p); s2 = sum(Fraction(1, u * v) for u in range(1, p) for v in range(1, p) if u + v >= p)
        Bform = p * p * m * m * sum(Rlucas(n1, n2, 0) * s1 + Rlucas(n1, n2, 1) * s2 for n1 in range(m) for n2 in range(m))
        Bok = vp(BU - Bform, p) >= 3
        # (K): expansions and assembled B(k)
        exp_bad = 0; Bk_bad = 0; blk_bad = 0
        def B0(n1): return C(m - 1, n1) ** 2 * C(m + n1, n1) * sum(C(m - 1, n1 + j1) ** 2 * C(m + j1 - 1, j1) for j1 in range(0, m))
        for k in range(1, N):
            if k % p == 0: continue
            n1 = k // p; H = Hp(k, p)
            if vp(C(N - 1, k) ** 2 - C(m - 1, n1) ** 2 * (1 - 2 * p * m * H), p) < 2: exp_bad += 1
            if vp(C(N + k - 1, k - 1) - C(m + n1, n1) * (1 + p * m * (H - Fraction(1, k))), p) < 2: exp_bad += 1
            for j1 in range(0, m):
                if vp(C(N - 1, k + p * j1) ** 2 - C(m - 1, n1 + j1) ** 2 * (1 - 2 * p * m * H), p) < 2: exp_bad += 1
                if vp(C(N + p * j1 - 1, p * j1) - C(m + j1 - 1, j1), p) < 3: exp_bad += 1
            Bk = C(N - 1, k) ** 2 * C(N + k - 1, k - 1) * sum(C(N - 1, k + p * j1) ** 2 * C(N + p * j1 - 1, p * j1) for j1 in range(0, m))
            if vp(Bk - B0(n1) * (1 - 3 * p * m * H - Fraction(p * m, k)), p) < 2: Bk_bad += 1
        for n1 in range(0, m):
            b1 = sum(Fraction(1, n1 * p + u) for u in range(1, p)); b2 = sum(Fraction(1, (n1 * p + u) ** 2) for u in range(1, p)); b3 = sum(Hp(n1 * p + u, p) / (n1 * p + u) for u in range(1, p))
            if vp(b1, p) < 2 or vp(b2, p) < 1 or vp(b3, p) < 1: blk_bad += 1
        SKsum = sum(Fraction(C(N - 1, k) ** 2 * C(N + k - 1, k - 1) * sum(C(N - 1, k + p * j1) ** 2 * C(N + p * j1 - 1, p * j1) for j1 in range(0, m)), k) for k in range(1, N) if k % p)
        Kid = (KU == N * SKsum); Kv = vp(SKsum, p) - 2
        # (J)
        def Bt0(n2): return C(m + n2, n2) * sum(C(m - 1, k1) ** 2 * C(m + k1 - 1, k1) * C(m - 1, k1 + n2) ** 2 for k1 in range(0, m))
        Bj_bad = 0
        for j in range(1, N):
            if j % p == 0: continue
            Bj = C(N + j - 1, j - 1) * sum(C(N - 1, p * k1) ** 2 * C(N + p * k1 - 1, p * k1) * C(N - 1, p * k1 + j) ** 2 for k1 in range(0, m))
            if vp(Bj - Bt0(j // p) * (1 - p * m * Hp(j, p) - Fraction(p * m, j)), p) < 2: Bj_bad += 1
        SJsum = sum(Fraction(C(N + j - 1, j - 1) * sum(C(N - 1, p * k1) ** 2 * C(N + p * k1 - 1, p * k1) * C(N - 1, p * k1 + j) ** 2 for k1 in range(0, m)), j) for j in range(1, N) if j % p)
        Jid = (JU == N * SJsum); Jv = vp(SJsum, p) - 2
        ok = (tot >= 0 and vp(SS - aM1, p) >= 3 and (tw >= 0) and qid and lucas_ok and Bok and vp(BU, p) >= 3 and exp_bad == 0 and Bk_bad == 0 and blk_bad == 0
              and Kid and Kv >= 0 and vp(KU, p) >= 3 and Bj_bad == 0 and Jid and Jv >= 0 and vp(JU, p) >= 3)
        def f(v): return "inf" if v >= INF else v
        report(f"sec5 p={p} m={m} N={N}", ok,
               f"Prop slack {tot}; S: sum {f(vp(SS-aM1,p)-3)} termwise {f(tw)} rewrite {qid}; B: lucas {lucas_ok}, block formula mod p^3 {Bok}, slack {f(vp(BU,p)-3)}; K: exp fails {exp_bad}, B(k) fails {Bk_bad}, blocksum fails {blk_bad}, id {Kid}, sum'B/k slack vs p^2 {f(Kv)}, slack {f(vp(KU,p)-3)}; J: B~(j) fails {Bj_bad}, id {Jid}, slack vs p^2 {f(Jv)}, slack {f(vp(JU,p)-3)}")
# Proposition over a wider grid incl. p | m
for p in (5, 7, 11, 13, 17, 19, 23):
    res = [(m, vp(a_def(m * p - 1) - a_def(m - 1), p) - 3) for m in list(range(1, 7)) + [p] if m * p <= 130]
    report(f"sec5 Proposition p={p}", all(v >= 0 for _, v in res), f"(m, slack) {res}")

print(f"\nSUMMARY rereview_oss_a376462: PASS {PASS}, FAIL {FAIL}")
