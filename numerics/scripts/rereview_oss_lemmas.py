# Independent re-review (2026-10-15) of Lemmas 1-4 of notes/A363983-proof.md, which are also used
# verbatim by notes/A376462-proof-first-congruence.md.  Exact arithmetic only (Fraction / comb).
# Run: ~/venvs/general/bin/python -I numerics/rereview_oss_lemmas.py > numerics/out/rereview_oss_lemmas.txt
from math import comb
from fractions import Fraction

INF = 10**9
def vp(x, p):
    x = Fraction(x)
    if x == 0: return INF
    a, b = x.numerator, x.denominator; v = 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v

def gbinom(a, k):
    """generalized binomial C(a,k), integer a (any sign), k>=0 integer."""
    if k < 0: return 0
    num = 1
    for i in range(k): num *= (a - i)
    den = 1
    for i in range(2, k + 1): den *= i
    return num // den

def gbinom_row(a, kmax):
    """[C(a,0), ..., C(a,kmax)] incrementally (exact)."""
    out = [1]; cur = 1
    for k in range(kmax):
        cur = cur * (a - k) // (k + 1)
        out.append(cur)
    return out

def vmin_int(x, p):
    return vp(x, p)

FAIL = 0; PASS = 0
def report(name, ok, detail=""):
    global FAIL, PASS
    if ok: PASS += 1
    else: FAIL += 1
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""))

# ---------------------------------------------------------------------------------------------
print("== Lemma 1 (Kazandzidis quotient form, Robert-Zuber): v_p(C(pA,pB)/C(A,B) - 1) >= 3 + v_p(A)+v_p(B)+v_p(A-B), p>=5, A>B>0")
for p, Amax in ((5, 70), (7, 56), (11, 44), (13, 39)):
    worst = INF; bad = 0; tot = 0; worst_at = None
    for A in range(2, Amax + 1):
        for B in range(1, A):
            q = Fraction(comb(p * A, p * B), comb(A, B))
            need = 3 + vp(A, p) + vp(B, p) + vp(A - B, p)
            got = vp(q - 1, p)
            tot += 1
            if got < need: bad += 1
            if got - need < worst: worst = got - need; worst_at = (A, B, got, need)
    report(f"Lemma1 p={p} A<={Amax}", bad == 0, f"{tot} pairs, failures {bad}, min slack {worst} at (A,B,got,need)={worst_at}")
# p = 3 control (the lemma is stated for p >= 5 only)
p = 3; worst = INF; bad = 0
for A in range(2, 40):
    for B in range(1, A):
        q = Fraction(comb(p * A, p * B), comb(A, B)); need = 3 + vp(A, p) + vp(B, p) + vp(A - B, p); got = vp(q - 1, p)
        if got < need: bad += 1
        worst = min(worst, got - need)
print(f"   control p=3: failures {bad} of {sum(range(1,39))}, min slack {worst} (expected negative: p>=5 hypothesis is needed)")

print("== Lemma 1 consequence: C(p^r a, p^s b)/C(p^{r-1}a, p^{s-1}b) == 1 mod p^{r+s+min(r,s)} (a,b>=1; incl. p|a, p|b; =1 when A=B; both 0 when B>A)")
for p in (5, 7, 11):
    worst = INF; bad = 0; tot = 0; zero_ok = True; worst_at = None
    for r in (1, 2, 3):
        for s in (1, 2, 3):
            for a in (1, 2, 3, 4, p, 2 * p):
                for b in (1, 2, 3, 4, p, 2 * p):
                    A = p ** (r - 1) * a; B = p ** (s - 1) * b
                    hi = comb(p ** r * a, p ** s * b) if p ** s * b <= p ** r * a else 0
                    lo = comb(A, B) if B <= A else 0
                    if B > A:
                        zero_ok &= (hi == 0 and lo == 0); continue
                    if A == B:
                        zero_ok &= (Fraction(hi, lo) == 1); continue
                    tot += 1
                    got = vp(Fraction(hi, lo) - 1, p); need = r + s + min(r, s)
                    if got < need: bad += 1
                    if got - need < worst: worst = got - need; worst_at = (r, s, a, b, got, need)
    report(f"Lemma1-consequence p={p}", bad == 0 and zero_ok, f"{tot} nontrivial cases, failures {bad}, min slack {worst} at (r,s,a,b,got,need)={worst_at}; trivial cases consistent {zero_ok}")

# ---------------------------------------------------------------------------------------------
print("== Lemma 2 (OSS 2.2, n=-2): full sum, lower half (k<p^s/2) and upper half (k>p^s/2) of k^{-2} over p∤k are == 0 mod p^s")
for p in (5, 7, 11, 13):
    for s in (1, 2, 3):
        full = sum(Fraction(1, k * k) for k in range(1, p ** s) if k % p)
        low = sum(Fraction(1, k * k) for k in range(1, p ** s) if k % p and 2 * k < p ** s)
        up = sum(Fraction(1, k * k) for k in range(1, p ** s) if k % p and 2 * k > p ** s)
        sl = (vp(full, p) - s, vp(low, p) - s, vp(up, p) - s)
        report(f"Lemma2 p={p} s={s}", min(sl) >= 0, f"slack (full, lower, upper) = {sl}")
for s in (1, 2, 3):
    p = 3
    full = sum(Fraction(1, k * k) for k in range(1, p ** s) if k % p)
    low = sum(Fraction(1, k * k) for k in range(1, p ** s) if k % p and 2 * k < p ** s)
    print(f"   control p=3 s={s}: slack full {vp(full,p)-s}, lower half {vp(low,p)-s}")

# ---------------------------------------------------------------------------------------------
print("== Lemma 3 (OSS 2.4): (-1)^k C(mp^r-1,k) == (-1)^[k/p] C(mp^{r-1}-1,[k/p]) mod p^r, incl. m<=0 (generalized binomials) and p|m")
for p in (5, 7, 11):
    for r in (1, 2, 3):
        ms = (-2, -1, 0, 1, 2, 3, p, 2 * p) if (p, r) != (11, 3) else (-1, 0, 1, 11)
        for m in ms:
            if p ** r * abs(max(m, 1)) > 20000: continue
            kmax = 2 * abs(m) * p ** r + 3 if m != 0 else 3 * p ** r + 3
            if kmax > 20000: kmax = 20000
            hi = gbinom_row(m * p ** r - 1, kmax)
            lo = gbinom_row(m * p ** (r - 1) - 1, kmax // p + 1)
            mod = p ** r; bad = 0; worst = INF
            for k in range(kmax + 1):
                d = (-1) ** k * hi[k] - (-1) ** (k // p) * lo[k // p]
                if d % mod: bad += 1
                if d: worst = min(worst, vp(d, p) - r)
            report(f"Lemma3 p={p} r={r} m={m} k<={kmax}", bad == 0, f"failures {bad}, min slack {worst if worst<INF else 'all equal'}")

# ---------------------------------------------------------------------------------------------
print("== Lemma 4(i) (OSS (27)): C(mp^r+k,k) == C(mp^{r-1}+[k/p],[k/p]) mod p^r")
for p in (5, 7, 11):
    for r in (1, 2, 3):
        for m in (1, 2, 3, p):
            n = m * p ** r
            if n > 20000: continue
            kmax = min(2 * n + 3, 20000)
            # C(n+k,k) incrementally
            mod = p ** r; bad = 0; worst = INF; cur = 1; lo_cache = {}
            for k in range(kmax + 1):
                if k > 0: cur = cur * (n + k) // k
                q = k // p
                if q not in lo_cache: lo_cache[q] = comb(m * p ** (r - 1) + q, q)
                d = cur - lo_cache[q]
                if d % mod: bad += 1
                if d: worst = min(worst, vp(d, p) - r)
            report(f"Lemma4(i) p={p} r={r} m={m} k<={kmax}", bad == 0, f"failures {bad}, min slack {worst if worst<INF else 'all equal'}")

print("== Lemma 4(ii) (OSS (28)): C(j,mp^r) == C([j/p],mp^{r-1}) mod p^r, for all j>=0 (both sides 0 when j<mp^r)")
def C(a, b): return comb(a, b) if 0 <= b <= a else 0
for p in (5, 7, 11):
    for r in (1, 2, 3):
        for m in (1, 2, 3, p):
            n = m * p ** r
            if n > 6000: continue
            jmax = 3 * n + 3
            mod = p ** r; bad = 0; worst = INF; zero_ok = True
            for j in range(jmax + 1):
                d = C(j, n) - C(j // p, m * p ** (r - 1))
                if j < n: zero_ok &= (C(j, n) == 0 and C(j // p, m * p ** (r - 1)) == 0)
                if d % mod: bad += 1
                if d: worst = min(worst, vp(d, p) - r)
            report(f"Lemma4(ii) p={p} r={r} m={m} j<={jmax}", bad == 0 and zero_ok, f"failures {bad}, min slack {worst if worst<INF else 'all equal'}, j<n both zero {zero_ok}")

print("== Identities used in both notes: C(N,k) = (N/k) C(N-1,k-1); C(N+k-1,k) = (N/k) C(N+k-1,k-1); C(X-1,Y) = ((X-Y)/X) C(X,Y)")
ok1 = all(Fraction(comb(N, k)) == Fraction(N, k) * comb(N - 1, k - 1) for N in range(1, 60) for k in range(1, N + 1))
ok2 = all(Fraction(comb(N + k - 1, k)) == Fraction(N, k) * comb(N + k - 1, k - 1) for N in range(1, 60) for k in range(1, 2 * N + 1))
ok3 = all(Fraction(comb(X - 1, Y)) == Fraction(X - Y, X) * comb(X, Y) for X in range(1, 60) for Y in range(0, X + 1))
report("identity C(N,k)=(N/k)C(N-1,k-1)", ok1); report("identity C(N+k-1,k)=(N/k)C(N+k-1,k-1)", ok2); report("identity C(X-1,Y)=((X-Y)/X)C(X,Y)", ok3)

print(f"\nSUMMARY rereview_oss_lemmas: PASS {PASS}, FAIL {FAIL}")
