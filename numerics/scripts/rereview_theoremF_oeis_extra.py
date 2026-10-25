#!/usr/bin/env python3
# Re-review supplement: the four OEIS sequences named in the Theorem F notes that are NOT in statements/STATEMENTS.md
# (A119259, A103885, A002003, A333564). Data below were copied from the OEIS b-files (oeis.org/Axxxxxx/bxxxxxx.txt)
# on 2026-10-15 and are treated as external, untrusted data: the checks are "does the note's A_(a,b,c) reproduce them".
# Output: numerics/out/rereview_theoremF_oeis_extra.txt
import os, time
from fractions import Fraction as Fr

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repository root
OUT = os.path.join(ROOT, 'numerics/out/rereview_theoremF_oeis_extra.txt')
LINES = []
def out(s=''):
    print(s); LINES.append(s)
NPASS = NFAIL = 0
def check(name, ok, detail=''):
    global NPASS, NFAIL
    if ok: NPASS += 1
    else: NFAIL += 1
    out(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ''))
def gbinom_list(e, K):
    r = [1]
    for i in range(1, K+1): r.append(r[-1] * (e - i + 1) // i)
    return r
def Acoef(a, b, c, N):
    K = c*N
    A = gbinom_list(a*N, K); B = gbinom_list(b*N, K)
    return sum(A[i] * B[K-i] * (-1)**(K-i) for i in range(K+1))
def v3(x):
    if x == 0: return 10**6
    v = 0
    while x % 3 == 0: x //= 3; v += 1
    return v

A119259 = [1,3,17,111,769,5503,40193,297727,2228225,16807935,127574017,973168639,7454392321,57298911231,441739706369,3414246490111,26447737520129,205272288591871,1595964714385409,12427568655368191,96905907580960769,756583504975757311,5913649000782757889,46270323833566134271,362376228141298352129,2840491845703386005503,22283045041232152625153,174934906856212768227327,1374282540281037601112065,10803197351632870578323455,84974097984303960730632193]
A103885 = [1,2,16,146,1408,14002,142000,1459810,15158272,158611106,1669752016,17664712562,187641279616,2000029880786,21380213588848,229129634462146,2460955893981184,26482855453375042,285475524009208720,3082024598888203090,33319523640218177408,360660931681855529458,3908294288344060883504,42395530826948622223906,460320026879092505248768,5002343894717275386764002,54404132534945443585817680,592118989004413904319421490,6448842091960218879699656320,70279631553683369649670453010,766361376426084008735563702000]
A002003 = [0,2,8,38,192,1002,5336,28814,157184,864146,4780008,26572086,148321344,830764794,4666890936,26283115038,148348809216,838944980514,4752575891144,26964373486406,153196621856192,871460014012682,4962895187697048,28292329581548718,161439727075246592,921991641870126002,5269738713907663016,30141904551115043414,172523643553950122304,988102791772527208986,5662556669152122153336,32468566408704598214718,186268135991213676920832,1069116700915117384267842,6139177238547480264595848,35268115657225046492723814,202689313141999060345545408,1165322955929802587157834282,6702236150940043341221087832,38560524436732069494872292558,221926083440378179880546717184,1277641371110176885906969191378,7357635677697822421448659479912,42382858308903823838653303894902,244207627796367536071847992477248,1407472689580038363741087860857146]
A333564 = {n: v for n, v in zip(range(1, 23), [2,8,56,384,2752,20096,148864,1114112,8403968,63787008,486584320,3727196160,28649455616,220869853184,1707123245056,13223868760064,102636144295936,797982357192704,6213784327684096,48452953790480384,378291752487878656,2956824500391378944])}

t0 = time.time()
out("Re-review supplement: OEIS sequences not in STATEMENTS.md (external b-file data, fetched 2026-10-15). " + time.strftime('%Y-%m-%d %H:%M'))
out("=" * 100)
check("A119259(n) = A_(2,-1,1)(n), n = 0..30 (b-file)", all(Acoef(2, -1, 1, n) == A119259[n] for n in range(31)))
check("A103885(n) = A_(1,-1,2)(n) = [x^{2n}]((1+x)/(1-x))^n, n = 0..30 (b-file)", all(Acoef(1, -1, 2, n) == A103885[n] for n in range(31)))
check("A002003(n) = A_(1,-1,1)(n) = [x^n]((1+x)/(1-x))^n for 1 <= n <= 45 (b-file); note says 'verified 1 <= n <= 40'", all(Acoef(1, -1, 1, n) == A002003[n] for n in range(1, 46)))
check("A002003(0) = 0 != A_(1,-1,1)(0) = 1 (as the note says)", A002003[0] == 0 and Acoef(1, -1, 1, 0) == 1)
check("A333564(n) = (A119259(n) - (-1)^n)/2 for 1 <= n <= 22 (b-file)", all((A119259[n] - (-1)**n) % 2 == 0 and (A119259[n] - (-1)**n)//2 == A333564[n] for n in range(1, 23)))
check("A333565 = 4*A333564 + (-1)^n = 2*A119259 - (-1)^n consistency, n = 1..22", all(4*A333564[n] + (-1)**n == 2*A119259[n] - (-1)**n for n in range(1, 23)))
check("p>=5 note section 6: A002003: v_3(a(3) - a(1)) = v_3(36) = 2", A002003[3] - A002003[1] == 36 and v3(36) == 2)
check("p=3 note section 0: v_3(A(3)-A(1)) = 2 for A352373=(-1,-3,1), A002003=(1,-1,1), A103885=(1,-1,2)", all(v3(Acoef(a, b, c, 3) - Acoef(a, b, c, 1)) == 2 for (a, b, c) in [(-1, -3, 1), (1, -1, 1), (1, -1, 2)]), f"values {[Acoef(a,b,c,3)-Acoef(a,b,c,1) for (a,b,c) in [(-1,-3,1),(1,-1,1),(1,-1,2)]]}")
# towers at p = 3 directly on b-file data (independent of our A_(a,b,c) code)
out("   p = 3 towers read off the b-files (v_3(a(3^r n) - a(3^{r-1} n)) vs 3r):")
for name, seq, good in (("A119259", {n: v for n, v in enumerate(A119259)}, True), ("A333564", A333564, True), ("A103885", {n: v for n, v in enumerate(A103885)}, False), ("A002003", {n: v for n, v in enumerate(A002003)}, False)):
    rows = []
    for (r, n) in [(1, 1), (1, 2), (1, 4), (1, 5), (1, 7), (1, 8), (1, 10), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1)]:
        N = n*3**r; M = n*3**(r-1)
        if N not in seq or M not in seq: continue
        rows.append(f"r{r}n{n}:{v3(seq[N]-seq[M])-3*r:+d}")
    out(f"     {name}: " + " ".join(rows))
    if good:
        check(f"{name} tower at p=3 holds on all b-file data available (slack >= 0)", all(int(x.split(':')[1]) >= 0 for x in rows))
# p = 5, 7 towers directly on b-file data where available
for name, seq, triple in (("A119259", {n: v for n, v in enumerate(A119259)}, (2, -1, 1)), ("A002003", {n: v for n, v in enumerate(A002003)}, (1, -1, 1)), ("A103885", {n: v for n, v in enumerate(A103885)}, (1, -1, 2))):
    def vq(x, p):
        if x == 0: return 10**6
        v = 0
        while x % p == 0: x //= p; v += 1
        return v
    rows = []
    for p in (5, 7):
        for n in (1, 2, 3, 4, 6, 8, 9):
            N = n*p
            if N in seq: rows.append(f"p{p}n{n}:{vq(seq[N]-seq[n], p)-3:+d}")
        if p*p in seq: rows.append(f"p{p}r2:{vq(seq[p*p]-seq[p], p)-6:+d}")
    check(f"{name} = A_{triple}: cubic tower r=1 (and r=2 where available) at p=5,7 on b-file data", all(int(x.split(':')[1]) >= 0 for x in rows), " ".join(rows))
out("\n" + "=" * 100)
out(f"SUMMARY: {NPASS} passed, {NFAIL} failed; elapsed {time.time()-t0:.1f}s")
open(OUT, 'w').write("\n".join(LINES) + "\n")
