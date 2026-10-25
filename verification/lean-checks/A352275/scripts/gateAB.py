"""Gates A and B for the A352275 Lean proof (u_m family).
Gate A: mirror the Lean target definition of u exactly (Q arithmetic, Rat.floor, Int.toNat) and compare with OEIS b-files.
Gate B: test every step of the planned Lean bridge numerically, with the exact Epoch definitions
(formalCatalanCoeff via Ring.choose, formalPartial, FNat via Qseries with qCoeff).
Usage: python3 -I gateAB.py <dir with b352275.txt b333093.txt b352276.txt>"""
import sys, os
from fractions import Fraction
from math import comb, floor

def u_target(m, n):
    # noncomputable def u (m n : N) : N := if n = 0 then 1 else sum_{k in range (m*n+1)} (Rat.floor (n/(n+2k) * C(n+2k,k))).toNat
    if n == 0:
        return 1
    s = 0
    for k in range(m * n + 1):
        q = Fraction(n, n + 2 * k) * comb(n + 2 * k, k)   # (n:Q)/(n+2k:Q) * choose ; n+2k>0 since n>=1
        f = floor(q)                                        # Rat.floor
        s += f if f > 0 else 0                              # Int.toNat
    return s

def gchoose(z, k):
    # Ring.choose z k for integer z: z(z-1)...(z-k+1)/k!
    num = 1
    for i in range(k):
        num *= (z - i)
    from math import factorial
    assert num % factorial(k) == 0
    return num // factorial(k)

def formalCatalanCoeff(r, k):
    return 1 if k == 0 else gchoose(r + 2 * k - 1, k) - gchoose(r + 2 * k - 1, k - 1)

def formalPartial(r, N):
    return sum(formalCatalanCoeff(r, k) for k in range(N + 1))

def qCoeff(n):
    return 1 if n == 0 else (2 if n % 3 == 0 else -1)

def FNat(A, B):
    # coeff_B ( Qseries * (1+X)^A ), (1+X)^A a polynomial with A natural
    return sum(qCoeff(B - j) * comb(A, j) for j in range(B + 1))

def vp(x, p):
    if x == 0:
        return 10**9
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        if fails <= 20:
            print("FAIL", msg)

bdir = sys.argv[1]
# ---------- Gate A: target definition vs OEIS b-files
for m, a in [(1, "333093"), (2, "352275"), (3, "352276")]:
    rows = []
    for line in open(os.path.join(bdir, f"b{a}.txt")):
        t = line.split()
        if len(t) == 2 and not line.startswith("#"):
            rows.append((int(t[0]), int(t[1])))
    nmax = rows[-1][0] if m != 2 else 400   # u_2: compare the first 401 rows (exact Q arithmetic is slow beyond)
    cnt = 0
    for n, val in rows:
        if n > nmax:
            break
        check(u_target(m, n) == val, f"Gate A: u_{m}({n}) != b{a}")
        cnt += 1
    print(f"Gate A: u_{m} vs A{a} b-file: {cnt} terms compared (n = 0..{min(nmax, rows[-1][0])})")

# ---------- Gate B1: term identity and non-negativity, for all k <= m*n
c = 0
for n in range(1, 61):
    for k in range(0, 6 * n + 1):
        q = Fraction(n, n + 2 * k) * comb(n + 2 * k, k)
        exp = 1 if k == 0 else comb(n + 2 * k - 1, k) - comb(n + 2 * k - 1, k - 1)
        check(q == exp, f"B1 term identity n={n} k={k}")
        check(exp >= 0, f"B1 nonneg n={n} k={k}")
        check(formalCatalanCoeff(n, k) == exp, f"B1 formalCatalanCoeff n={n} k={k}")
        c += 1
print(f"Gate B1: term identity, integrality, non-negativity, = formalCatalanCoeff n k: {c} pairs (n<=60, k<=6n)")

# ---------- Gate B2: u m n = formalPartial n (m n) = FNat ((2m+1) n) (m n)
c = 0
for m in range(0, 7):
    for n in range(1, 41):
        U = u_target(m, n)
        check(U == formalPartial(n, m * n), f"B2 u=formalPartial m={m} n={n}")
        check(U == FNat((2 * m + 1) * n, m * n), f"B2 u=FNat m={m} n={n}")
        c += 1
print(f"Gate B2: u m n = formalPartial n (mn) = FNat((2m+1)n, mn): {c} pairs (m<=6, n<=40)")

# ---------- Gate B3: formalPartial_eq_FNat as stated (A, N naturals; r = A - 2N may be negative)
c = 0
for A in range(0, 61):
    for N in range(0, 31):
        check(formalPartial(A - 2 * N, N) == FNat(A, N), f"B3 formalPartial(A-2N,N)=FNat(A,N) A={A} N={N}")
        c += 1
print(f"Gate B3: formalPartial (A-2N) N = FNat A N: {c} pairs (A<=60, N<=30)")

# ---------- Gate B4: the scaling step exactly as it will be applied, and the final congruence
c = 0; minslack = None
for p in [5, 7, 11, 13]:
    for m in range(0, 5):
        for n in range(1, 4):
            for r in range(1, 3):
                Nn = n * p ** (r - 1)
                B, Y, lev = m * Nn, (m + 1) * Nn, r - 1
                check(B % p ** lev == 0 and Y % p ** lev == 0, "B4 divisibility")
                check(p * (B + Y) == (2 * m + 1) * n * p ** r and p * B == m * n * p ** r, "B4 index arithmetic")
                lhs = FNat(p * (B + Y), p * B); rhs = FNat(B + Y, B)
                v = vp(lhs - rhs, p)
                check(v >= 3 * (lev + 1), f"B4 scaling p={p} m={m} n={n} r={r} v={v}")
                if n * p ** r <= 200:   # exact target definition where affordable
                    U1, U0 = u_target(m, n * p ** r), u_target(m, n * p ** (r - 1))
                    check(U1 == lhs and U0 == rhs, f"B4 u vs FNat p={p} m={m} n={n} r={r}")
                    vt = vp(U1 - U0, p)
                    check(vt >= 3 * r, f"B4 target congruence p={p} m={m} n={n} r={r}")
                s = v - 3 * r
                minslack = s if minslack is None else min(minslack, s)
                c += 1
print(f"Gate B4: scaling lemma as applied and target congruence: {c} cases (p in 5,7,11,13; m<=4; n<=3; r<=2); min slack {minslack}")
print(f"FAILURES: {fails}")
