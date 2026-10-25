# Re-review (fact-only) of notes/A386548-quadratic-tower-proof.md -- congruences, at the stated moduli, with slack.
# Run: ~/venvs/general/bin/python -I numerics/rereview_quad_A386548_congruences.py > numerics/out/rereview_quad_A386548_congruences.txt
# C1  (JK) quotient form: v_p(C(pA,pB)/C(A,B) - 1) - (3 + v(A) + v(B) + v(A-B)) >= 0, p in {5,7,11,13}, 1<=B<A<=70 ; p=3 with 2+... ; p=2 fails
# C2  level form: p^s | A, p^s | B  =>  C(pA,pB)/C(A,B) == 1 mod p^{3(s+1)}  (p in {5,7,11}, s<=2)
# C3  unscaled terms: v_p(C(N,j)C(N+k-1,k)) >= 2R for p∤j, 2j+3k=N   (R = v_p(N))
# C4  scaled terms: v_p(T_N - T_M) >= 3R for every scaled pair; per-case check of the chain
#       case s<R-1: v(Q1Q2-1) >= R+2+2s and v(T_M) >= 2(R-1-s);  case s>=R-1: v(Q1-1),v(Q2-1) >= 3R
# C5  theorem: v_p(a(np^r) - a(np^{r-1})) >= 2r for p in {5,7,11,13}, n<=6 and n=p (p|n), r<=3 (N<=1600); exactness (=2r) recorded
# C6  remark (i): v_p(sum of unscaled terms) == 2R exactly?  recorded
# C7  p=3 data: v_3(a(3^r)-a(3^{r-1})) for r=1,2,3 and n=2
# C8  remark (ii) family test: [x^{cN}]((1+eps x^u)/(1-del x^v))^N quadratic tower at odd p ∤ uv  (p=3 included when 3∤uv)
from fractions import Fraction
from math import comb

def vp(x, p):
    x = Fraction(x)
    if x == 0:
        return 10**9
    a, b = x.numerator, x.denominator
    v = 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v

fails = 0; passes = 0
def check(cond, msg):
    global fails, passes
    if cond:
        passes += 1
    else:
        fails += 1
        print("FAIL:", msg)

# C1
print("== C1 (JK) quotient form ==")
for p in (5, 7, 11, 13):
    worst = 10**9; where = None; cnt = 0
    for A in range(2, 71):
        for B in range(1, A):
            lhs = vp(Fraction(comb(p * A, p * B), comb(A, B)) - 1, p)
            rhs = 3 + vp(A, p) + vp(B, p) + vp(A - B, p)
            cnt += 1
            if lhs - rhs < worst:
                worst = lhs - rhs; where = (A, B, lhs, rhs)
            check(lhs >= rhs, f"C1 p={p} A={A} B={B} lhs={lhs} rhs={rhs}")
    print(f"  p={p}: {cnt} pairs, min slack {worst} at (A,B,lhs,rhs)={where}")
# p = 3 with exponent 2 (Robert-Zuber's p=3 statement) and p=3 with exponent 3 (should fail)
for p, base in ((3, 2), (3, 3), (2, 3)):
    worst = 10**9; where = None
    for A in range(2, 61):
        for B in range(1, A):
            lhs = vp(Fraction(comb(p * A, p * B), comb(A, B)) - 1, p)
            rhs = base + vp(A, p) + vp(B, p) + vp(A - B, p)
            if lhs - rhs < worst:
                worst = lhs - rhs; where = (A, B, lhs, rhs)
    print(f"  p={p} with constant {base}: min slack {worst} at {where}")

# C2
print("== C2 level form ==")
for p in (5, 7, 11):
    worst = 10**9
    for s in (0, 1, 2):
        step = p ** s
        for A in range(step, 30 * step + 1, step):
            for B in range(step, A, step):
                d = vp(Fraction(comb(p * A, p * B), comb(A, B)) - 1, p) - 3 * (s + 1)
                worst = min(worst, d)
                check(d >= 0, f"C2 p={p} s={s} A={A} B={B}")
    print(f"  p={p}: min slack {worst}")

# C3-C6
def a_formula1(N):
    tot = 0
    for k in range(0, N // 3 + 1):
        rem = N - 3 * k
        if rem % 2:
            continue
        j = rem // 2
        tot += (-1) ** (j + k) * comb(N, j) * (1 if k == 0 else comb(N + k - 1, k))  # C(-1,0)=1 convention at N=0
    return tot

print("== C3-C6 term-by-term and theorem ==")
exact = []
for p in (5, 7, 11, 13):
    for r in (1, 2, 3):
        for n in (1, 2, 3, 4, 5, 6, p):
            N = n * p ** r
            if N > 1600:
                continue
            M = N // p
            R = vp(N, p)
            uns_sum = 0; uns_min = 10**9; sc_min = 10**9
            case1_minQ = 10**9; case1_minT = 10**9; case2_min = 10**9
            for k in range(0, N // 3 + 1):
                rem = N - 3 * k
                if rem % 2:
                    continue
                j = rem // 2
                term = (-1) ** (j + k) * comb(N, j) * comb(N + k - 1, k)
                if j % p:
                    v = vp(term, p); uns_min = min(uns_min, v); uns_sum += term
                    check(v >= 2 * R, f"C3 unscaled p={p} N={N} j={j} k={k} v={v} < 2R={2*R}")
                else:
                    jp, kp = j // p, k // p
                    D = M + kp
                    TN = comb(N, j) * comb(N + k - 1, k)
                    TM = comb(M, jp) * comb(M + kp - 1, kp)
                    v = vp(TN - TM, p); sc_min = min(sc_min, v)
                    check(v >= 3 * R, f"C4 scaled p={p} N={N} j'={jp} k'={kp} v(T_N-T_M)={v} < 3R={3*R}")
                    Q1 = Fraction(comb(p * M, p * jp), comb(M, jp)); Q2 = Fraction(comb(p * D, p * kp), comb(D, kp))
                    s = min(vp(jp, p), vp(kp, p))
                    if s < R - 1:
                        vq = vp(Q1 * Q2 - 1, p); vt = vp(TM, p)
                        check(vq >= R + 2 + 2 * s, f"C4 case1 v(Q1Q2-1)={vq} < R+2+2s={R+2+2*s} p={p} N={N} j'={jp} k'={kp}")
                        check(vp(Q1 - 1, p) >= 3 + (R - 1) + 2 * s, f"C4 case1 Q1 p={p} N={N} j'={jp}")
                        check(vp(Q2 - 1, p) >= 3 + (R - 1) + 2 * s, f"C4 case1 Q2 p={p} N={N} k'={kp}")
                        check(vt >= 2 * (R - 1 - s), f"C4 case1 v(T_M)={vt} < 2(R-1-s) p={p} N={N}")
                        case1_minQ = min(case1_minQ, vq - (R + 2 + 2 * s)); case1_minT = min(case1_minT, vt - 2 * (R - 1 - s))
                    else:
                        v1 = vp(Q1 - 1, p) if jp else 10**9; v2 = vp(Q2 - 1, p) if kp else 10**9
                        check(v1 >= 3 * R and v2 >= 3 * R, f"C4 case2 p={p} N={N} j'={jp} k'={kp} v(Q1-1)={v1} v(Q2-1)={v2}")
                        case2_min = min(case2_min, min(v1, v2) - 3 * R)
            dv = vp(a_formula1(N) - a_formula1(M), p)
            check(dv >= 2 * r, f"C5 theorem p={p} n={n} r={r} v={dv} < 2r")
            vu = vp(uns_sum, p)
            exact.append((p, n, r, dv))
            print(f"  p={p} n={n} r={r} (R={R}): v(a(N)-a(M))={dv} [2r={2*r}, 2R={2*R}] | unscaled: min term v={uns_min}, v(sum)={vu} | scaled: min v(T_N-T_M)={sc_min} (3R={3*R}) | case1 slack (Q,T_M)=({case1_minQ},{case1_minT}) case2 slack={case2_min}")
print("  C5/C6 exactness: cases with v(a(N)-a(M)) != 2R:", [(p, n, r, dv) for (p, n, r, dv) in exact if dv != 2 * vp(n * p ** r, p)])
print("  C5 specific (13,3,2):", [(p, n, r, dv) for (p, n, r, dv) in exact if (p, n, r) == (13, 3, 2)])

# C7
print("== C7 p=3 ==")
print("  v_3(a(3^r)-a(3^(r-1))) r=1,2,3:", [vp(a_formula1(3 ** r) - a_formula1(3 ** (r - 1)), 3) for r in (1, 2, 3)])
print("  v_3(a(2*3^r)-a(2*3^(r-1))) r=1,2,3:", [vp(a_formula1(2 * 3 ** r) - a_formula1(2 * 3 ** (r - 1)), 3) for r in (1, 2, 3)])

# C8 remark (ii): general family  [x^{cN}] ((1+eps x^u)/(1-del x^v))^N
def fam(N, u, v, eps, dl, c):
    # (1+eps x^u)^N = sum_j eps^j C(N,j) x^{uj};  (1-del x^v)^{-N} = sum_k del^k C(N+k-1,k) x^{vk}
    tot = 0
    for k in range(0, (c * N) // v + 1):
        rem = c * N - v * k
        if rem < 0 or rem % u:
            continue
        j = rem // u
        if j > N:
            continue
        tot += (eps ** j) * (dl ** k) * comb(N, j) * comb(N + k - 1, k)
    return tot

print("== C8 remark (ii) family (quadratic tower at odd p ∤ uv) ==")
fam_fail = 0
for (u, v, eps, dl, c) in ((2, 3, -1, -1, 1), (2, 3, 1, 1, 1), (1, 2, 1, 1, 1), (2, 1, 1, 1, 1), (1, 3, 1, -1, 1), (3, 2, -1, 1, 1),
                           (2, 5, 1, 1, 1), (4, 3, 1, 1, 1), (2, 3, -1, -1, 2), (1, 2, -1, 1, 2), (3, 4, 1, -1, 1), (5, 2, -1, -1, 1)):
    row = []
    for p in (3, 5, 7, 11):
        if (u * v) % p == 0:
            continue
        for r in (1, 2):
            for n in (1, 2):
                N = n * p ** r
                if N > 250:
                    continue
                d = fam(N, u, v, eps, dl, c) - fam(N // p, u, v, eps, dl, c)
                val = vp(d, p)
                row.append((p, n, r, val))
                if val < 2 * r:
                    fam_fail += 1
                    print(f"  FAMILY FAILURE (u,v,eps,del,c)={(u,v,eps,dl,c)} p={p} n={n} r={r} v={val} < 2r")
    print(f"  (u,v,eps,del,c)={(u,v,eps,dl,c)}: (p,n,r,v) = {row}")
print("  family failures:", fam_fail)
print(f"PASS {passes} FAIL {fails}")
