# Independent re-review (2026-10-15) of notes/A363983-proof.md: Lemma 5, (1), (2), (3), Lemma 6, Theorem, Remarks.
# Exact arithmetic (Fraction / comb).  Includes r=3, p in {5,7,11}, p | m, k=N edge, both half blocks.
# Run: ~/venvs/general/bin/python -I numerics/rereview_oss_a363983.py > numerics/out/rereview_oss_a363983.txt
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
def sl(v, need): return "inf" if v >= INF else v - need

FAIL = 0; PASS = 0
def report(name, ok, detail=""):
    global FAIL, PASS
    if ok: PASS += 1
    else: FAIL += 1
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""))

def A(N, k):  # summand for N>=1, k>=1 (note's A(n,k))
    return (-1) ** (N + k) * C(N, k) * C(N + k - 1, k) * C(2 * k, N)
def a_oeis_def(n):  # literal OEIS definition with floor((n+1)/2) lower limit; n=0 term is C(-1,0)=1
    if n == 0: return 1
    return sum((-1) ** (n + k) * comb(n, k) * comb(n + k - 1, k) * comb(2 * k, n) for k in range((n + 1) // 2, n + 1))
def a(n):
    if n == 0: return 1
    return sum(A(n, k) for k in range(1, n + 1))
def D(n, k, j): return (-1) ** k * C(n - 1, k) * C(n + k, k) * C(j, n)

# ---------------------------------------------------------------------------------------------
print("== Statement: a(n) against OEIS A363983 data (statements/STATEMENTS.md)")
oeis = [1, 2, 14, 128, 1310, 14252, 161168, 1872096, 22179102, 266766500, 3247293764, 39914850560, 494587904720, 6170138404640, 77420709800000]
mine = [a_oeis_def(n) for n in range(len(oeis))]
report("OEIS data n=0..14 (literal definition)", mine == oeis, str(mine[:8]))
report("a(n) = sum_{k=1}^n A(n,k) for n=1..60 equals literal definition", all(a(n) == a_oeis_def(n) for n in range(1, 61)))

# ---------------------------------------------------------------------------------------------
print("== Lemma 5: A(mp^r, kp^s) == A(mp^{r-1}, kp^{s-1}) mod p^{3r} for p∤k, r,s>=1 (also p|m); plus the sub-claims")
GRID = [(5, 1, (1, 2, 3, 5, 10)), (5, 2, (1, 2, 3, 5)), (5, 3, (1, 2, 3, 5)), (7, 1, (1, 2, 3, 7, 14)), (7, 2, (1, 2, 3, 7)), (7, 3, (1, 2, 3)),
        (11, 1, (1, 2, 3, 11)), (11, 2, (1, 2, 3, 11)), (11, 3, (1, 2))]
t0 = time.time()
for p, r, ms in GRID:
    for m in ms:
        N = m * p ** r; M = N // p
        worst = INF; bad = 0; tot = 0; q2id = True; nonvan = True; qbad = 0; valbad = 0; worst_at = None
        for s in range(1, r + 2):
            for k in range(1, N // p ** s + 2):
                if k % p == 0: continue
                K = k * p ** s; Kp = k * p ** (s - 1)
                hi = A(N, K) if K <= N else 0; lo = A(M, Kp) if Kp <= M else 0
                nonvan &= ((hi != 0) == (lo != 0))
                d = hi - lo; tot += 1
                v = vp(d, p)
                if v < 3 * r: bad += 1
                if v - 3 * r < worst: worst = v - 3 * r; worst_at = (s, k)
                # sub-claims (only when the binomials are nonzero at the lower level)
                if Kp <= M:
                    # Q2 rewriting identity: C(N+K-1,K)/C(M+Kp-1,Kp) = C(N+K,K)/C(M+Kp,Kp)
                    q2id &= Fraction(C(N + K - 1, K), C(M + Kp - 1, Kp)) == Fraction(C(N + K, K), C(M + Kp, Kp))
                    need = r + s + min(r, s)
                    if 0 < Kp < M:
                        if vp(Fraction(C(N, K), C(M, Kp)) - 1, p) < need: qbad += 1
                    if vp(Fraction(C(N + K, K), C(M + Kp, Kp)) - 1, p) < need: qbad += 1
                    if M < 2 * Kp:
                        if vp(Fraction(C(2 * K, N), C(2 * Kp, M)) - 1, p) < need: qbad += 1
                    if s <= r and lo != 0:
                        if vp(lo, p) < 2 * (r - s): valbad += 1
                        if vp(C(M, Kp), p) < r - s or vp(C(M + Kp - 1, Kp), p) < r - s: valbad += 1
        report(f"Lemma5 p={p} r={r} m={m} (N={N}, s<={r+1})", bad == 0 and q2id and nonvan and qbad == 0 and valbad == 0,
               f"{tot} terms, failures {bad}, min slack {sl(worst+3*r,3*r) if worst<INF else 'all equal'} at (s,k)={worst_at}; Q2-rewrite exact {q2id}; nonvanishing agree {nonvan}; quotient-modulus failures {qbad}; valuation-bound failures {valbad}")
print(f"   (Lemma 5 block took {time.time()-t0:.1f}s)")

# ---------------------------------------------------------------------------------------------
print("== (1) a(N) - a(M) == G_0(N) mod p^{3r};  (2) G_0(N) = (-1)^N N^2 S exactly;  (3) S == -Sigma_1 mod p^r;  Lemma 6 chain;  Theorem")
t0 = time.time()
for p, r, ms in GRID:
    for m in ms:
        N = m * p ** r; M = N // p
        if N > 4000: continue
        aN = a(N); aM = a(M)
        G0 = sum(A(N, k) for k in range(1, N + 1) if k % p)
        S = sum(Fraction((-1) ** k * C(N - 1, k - 1) * C(N + k - 1, k - 1) * C(2 * k, N), k * k) for k in range(1, N + 1) if k % p)
        e1 = vp(aN - aM - G0, p); e2 = (G0 == (-1) ** N * N * N * S)
        sig = []
        for s in range(1, r + 1):
            n_lvl = m * p ** (r - s)
            cache = {}
            tot = Fraction(0)
            for k in range(1, N + 1):
                if k % p == 0: continue
                key = (k // p ** s, 2 * k // p ** s)
                if key not in cache: cache[key] = D(n_lvl, key[0], key[1])
                tot += Fraction(cache[key], k * k)
            sig.append(tot)
        e3 = vp(S + sig[0], p)
        chain = [vp(sig[i] - sig[i + 1], p) - r for i in range(r - 1)]
        er = vp(sig[-1], p) - r
        thm = vp(aN - aM, p) - 3 * r
        ok = e1 >= 3 * r and e2 and e3 >= r and all(c >= 0 for c in chain) and er >= 0 and thm >= 0
        report(f"(1)(2)(3)L6/Thm p={p} r={r} m={m} N={N}", ok,
               f"v(a(N)-a(M)-G0)-3r={sl(e1,3*r)}; (2) exact {e2}; v(S+Sigma_1)-r={sl(e3,r)}; chain slacks {chain}; v(Sigma_r)-r={er if er<INF else 'inf'}; THEOREM slack {thm}; v_p(N^2)-2r={vp(N*N,p)-2*r}")
print(f"   (block took {time.time()-t0:.1f}s)")

# ---------------------------------------------------------------------------------------------
print("== Lemma 6 internals: (a) [2k/p^s] = 2[k/p^s] + [{k}_s > p^s/2]; (b) each half-block inner sum of k^{-2} (p∤k) == 0 mod p^s; (c) D(mp^t,n,j) == D(mp^{t-1},[n/p],[j/p]) mod p^t")
ok_a = True
for p in (5, 7, 11):
    for s in (1, 2, 3):
        ps = p ** s
        for k in range(0, 3 * ps + 5):
            rem = k - ps * (k // ps)
            ok_a &= (2 * k // ps == 2 * (k // ps) + (1 if 2 * rem > ps else 0))
report("(a) floor identity", ok_a)
for p in (5, 7, 11):
    for s in (1, 2, 3):
        ps = p ** s; worst = INF; bad = 0
        for n in range(0, 4):
            lowsum = sum(Fraction(1, k * k) for k in range(n * ps, (n + 1) * ps) if k % p and 2 * (k - n * ps) < ps)
            upsum = sum(Fraction(1, k * k) for k in range(n * ps, (n + 1) * ps) if k % p and 2 * (k - n * ps) > ps)
            for x in (lowsum, upsum):
                v = vp(x, p)
                if v < s: bad += 1
                worst = min(worst, v - s)
        report(f"(b) half-block sums p={p} s={s} blocks n<4", bad == 0, f"min slack {worst}")
for p in (5, 7, 11):
    for t in (1, 2, 3):
        for m in (1, 2, p):
            n_hi = m * p ** t
            if n_hi > 2000: continue
            bad = 0; tot = 0; worst = INF
            for n in range(0, 2 * n_hi + 3):
                for j in (2 * n, 2 * n + 1, 2 * n - 1, 0):
                    if j < 0: continue
                    d = D(n_hi, n, j) - D(n_hi // p, n // p, j // p); tot += 1
                    if d % p ** t: bad += 1
                    if d: worst = min(worst, vp(d, p) - t)
            report(f"(c) D self-similarity p={p} t={t} m={m}", bad == 0, f"{tot} cases, failures {bad}, min slack {worst if worst<INF else 'all equal'}")

# ---------------------------------------------------------------------------------------------
print("== Remarks (section 5): signed family F(n) = sum_k (-1)^{n+k} C(n,k)^A C(n+k-1,k)^B C(2k,n)^C; claim: cubic tower for A,B>=1 and for A>=3,B=0; fails for (2,0,1)")
def F(n, Aa, Bb, Cc):
    if n == 0: return 1
    return sum((-1) ** (n + k) * C(n, k) ** Aa * C(n + k - 1, k) ** Bb * C(2 * k, n) ** Cc for k in range(0, n + 1))
f = lambda n: F(n, 2, 0, 1)
print(f"   signed (2,0,1): f(1)={f(1)}, f(5)={f(5)}, v_5(f(5)-f(1)) = {vp(f(5)-f(1),5)} (note/referee: 2 < 3)")
for (Aa, Bb, Cc) in ((1, 1, 1), (1, 1, 2), (2, 1, 1), (1, 2, 1), (3, 0, 1), (1, 1, 0), (3, 0, 0), (4, 0, 2)):
    res = []
    worst = INF
    for p in (5, 7):
        for r in (1, 2):
            for m in (1, 2):
                v = vp(F(m * p ** r, Aa, Bb, Cc) - F(m * p ** (r - 1), Aa, Bb, Cc), p) - 3 * r
                worst = min(worst, v); res.append(v)
    report(f"family (A,B,C)=({Aa},{Bb},{Cc}) p in 5,7; r<=2; m<=2", worst >= 0, f"slacks {res}")
for (Aa, Bb, Cc) in ((2, 0, 1), (2, 0, 2), (1, 0, 1), (0, 1, 1), (0, 2, 1)):
    res = [vp(F(m * p ** r, Aa, Bb, Cc) - F(m * p ** (r - 1), Aa, Bb, Cc), p) - 3 * r for p in (5, 7) for r in (1, 2) for m in (1, 2)]
    print(f"   not-covered family (A,B,C)=({Aa},{Bb},{Cc}): slacks vs 3r {res}  (negative = cubic tower fails)")
print("   p=3 for A363983 itself (proof excludes p=3):", [(r, m, vp(a(m * 3 ** r) - a(m * 3 ** (r - 1)), 3) - 3 * r) for r in (1, 2, 3) for m in (1, 2)])

print(f"\nSUMMARY rereview_oss_a363983: PASS {PASS}, FAIL {FAIL}")
