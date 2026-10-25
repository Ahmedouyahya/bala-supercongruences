"""Re-review of notes/A376462-shifted-congruence-proof.md, part (d): the
section-8 claims about Beukers (1985).

 1. Beukers' (10) (k = 0 case): sum_{n<p^t} H'_n = p^t H'_{p^t-1} - (p^t - p^{t-1})
    exactly, hence = p^{t-1} mod p^t (so (10) is FALSE for k = 0); the
    example sum_{n<5} H'_n = 77/12 = 1 mod 5.
 2. For which k does sum_{n<p^t} n^k H'_n = 0 mod p^t hold / fail (k=0..8)?
    And Beukers' own form sum_{n<p^t} k! C(n,k) H'_n.
 3. The note's explanation "the j = 0 and j = 1 terms of the expansion of
    sigma_s(n) cancel": expansion sigma_s(n) = sum_j (-p^s)^j n^j S_{j+1}(p^s-1)
    (base block, n < p^t); valuations of the j=0 term, j=1 term, their sum,
    and the j>=2 terms, versus t+2s.
 4. Beukers' Lemma 4(ii) as printed (mod p^{t+s}) versus the strong form
    (mod p^{t+2s}): actual valuations (base block and general blocks).
 5. The count on Beukers' pp. 153-154 for the zeta(2) Apery numbers:
    the stratum (13) is = 0 mod p^{2r}; the Lemma-3(ii) sum
    sum'_k (1/k) H'_{kp^s} C(mp^{r-s}-1,k)^2 C(-mp^{r-s}-1,k-1)(-1)^k has
    valuation >= r+s (strong form) and NOT merely >= r (printed count gives
    only (r-s)+s+(r-s) = 2r-s for the stratum).

Output: numerics/out/rereview_shifted_literature.txt
"""
import os
import sys
from fractions import Fraction
from math import comb, factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import ModHarm, Harm, Tally, tally_valmod, vp, gbinom, INF

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_literature.txt")
E = 30


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (d): literature claims of section 8")

        # 1.
        T.log("1. sum_{n<p^t} H'_n = p^t H'_{p^t-1} - (p^t - p^{t-1}) exactly;  = p^{t-1} mod p^t")
        Hm5 = Harm(5)
        s5 = sum(Hm5.H(n) for n in range(5))
        T.log(f"   sum_{{n<5}} H'_n = {s5}  (note says 77/12); residue mod 5 = {(s5.numerator * pow(s5.denominator, -1, 5)) % 5}  (note says 1)")
        T.check("sum_{n<5} H'_n = 77/12", s5 == Fraction(77, 12))
        T.check("77/12 = 1 mod 5", (s5.numerator * pow(s5.denominator, -1, 5)) % 5 == 1)
        for p in (5, 7, 11, 13):
            Hm = Harm(p)
            for t in (1, 2, 3):
                pt = p ** t
                if pt > 1400:
                    continue
                tot = sum(Hm.H(n) for n in range(pt))
                T.check("exact formula sum H'_n = p^t H'_{p^t-1} - (p^t - p^{t-1})", tot == pt * Hm.H(pt - 1) - (pt - pt // p), f"p={p} t={t}")
                d = tot - pt // p
                T.val("sum_{n<p^t} H'_n - p^{t-1} = 0 mod p^t", d, t, p, f"p={p} t={t}")
                T.check("hence (10) with k=0 FAILS: v(sum H'_n) = t-1 < t", vp(tot, p) == t - 1, f"p={p} t={t} v={vp(tot, p)}")

        # 2.
        T.log("2. sum_{n<p^t} n^k H'_n mod p^t and Beukers' k! C(n,k) form, k = 0..8")
        for p in (5, 7):
            MH = ModHarm(p, E)
            for t in (1, 2, 3):
                pt = p ** t
                row = []
                row2 = []
                for k in range(0, 9):
                    s = sum(pow(n, k, MH.P) * MH.H(n) for n in range(pt)) % MH.P
                    s2 = sum(factorial(k) * comb(n, k) % MH.P * MH.H(n) for n in range(pt)) % MH.P
                    row.append(MH.val(s))
                    row2.append(MH.val(s2))
                T.log(f"   p={p} t={t}: v(sum n^k H'_n) for k=0..8 = {row}  (need >= {t});  v(sum k!C(n,k)H'_n) = {row2}")
                T.check("(10) fails for k=0 (both forms)", row[0] < t and row2[0] < t, f"p={p} t={t}")

        # 3.
        T.log("3. Expansion of sigma_s(n), base block: term_j = (-p^s)^j S_{j+1}(p^s-1) sum_{n<p^t} n^j H'_n")
        for p in (5, 7):
            MH = ModHarm(p, E)
            P = MH.P
            for s in (1, 2):
                for t in (1, 2, 3):
                    if p ** (t + s) > 20000:
                        continue
                    pt, ps = p ** t, p ** s
                    terms = []
                    for j in range(0, 6):
                        Sj = MH.Sd(j + 1, ps - 1)
                        mom = sum(pow(n, j, P) * MH.H(n) for n in range(pt)) % P
                        terms.append((-ps) ** j * Sj % P * mom % P)
                    v0, v1 = MH.val(terms[0]), MH.val(terms[1])
                    v01 = MH.val((terms[0] + terms[1]) % P)
                    rest = [MH.val(x) for x in terms[2:]]
                    T.log(f"   p={p} s={s} t={t}: v(j=0 term)={v0}, v(j=1 term)={v1}, v(j=0 + j=1)={v01}, v(j>=2 terms)={rest}; needed t+2s={t + 2 * s}")
                    T.check("j=0 term alone is NOT = 0 mod p^{t+2s} (so Beukers' reduction fails)", v0 < t + 2 * s, f"p={p} s={s} t={t}")
                    tally_valmod(T, "j=0 + j=1 terms together = 0 mod p^{t+2s}", (terms[0] + terms[1]) % P, t + 2 * s, MH, f"p={p} s={s} t={t}")
                    for j, x in enumerate(terms[2:], start=2):
                        tally_valmod(T, "j>=2 terms each = 0 mod p^{t+2s}", x, t + 2 * s, MH, f"p={p} s={s} t={t} j={j}")
                    # full sum check: sum_j terms == Sigma(0) mod p^{t+2s+something}? (series truncated; just the lemma)
                    tot = sum(MH.sigma(s, n) * MH.H(n) for n in range(pt)) % P
                    tally_valmod(T, "Lemma 2.5 base block (= Beukers 4(i), i=0)", tot, t + 2 * s, MH, f"p={p} s={s} t={t}")

        # 4.
        T.log("4. Beukers' Lemma 4(ii) printed modulus p^{t+s} vs strong p^{t+2s}: actual valuations")
        for p in (5, 7, 11):
            MH = ModHarm(p, E)
            P = MH.P
            for s in (1, 2):
                for t in (1, 2):
                    for i in (0, 1, 2):
                        if (i + 1) * p ** (t + s) > 60000:
                            continue
                        tot = sum(pow(k, -1, P) * MH.H(k * p ** s) for k in range(i * p ** t, (i + 1) * p ** t) if k % p) % P
                        v = MH.val(tot)
                        T.log(f"   p={p} s={s} t={t} i={i}: v = {v}; printed t+s = {t + s}; strong t+2s = {t + 2 * s}")
                        T.check("strong form holds", v >= t + 2 * s, f"p={p} s={s} t={t} i={i}")

        # 5.
        T.log("5. Beukers pp.153-154 count, zeta(2) Apery numbers u_n = sum C(n,k)^2 C(n+k,k)")
        for p in (5, 7):
            for (m, r) in ((1, 2), (2, 2), (1, 3)):
                MH = ModHarm(p, 3 * r + 20)
                P = MH.P
                M = m * p ** (r - 1)
                for s in range(1, r):
                    # stratum (13): sum over k with v_p(kp) = s of H'_{kp} C(M-1,k)^2 C(-M,k) (-1)^k, k < M
                    strat = 0
                    for k in range(1, M):
                        if vp(p * k, p) != s:
                            continue
                        strat += MH.H(p * k) * (comb(M - 1, k) ** 2 % P) % P * (comb(M + k - 1, k) % P)
                    strat %= P
                    tally_valmod(T, "Beukers (13) stratum = 0 mod p^{2r} (true statement)", strat, 2 * r, MH, f"p={p} m={m} r={r} s={s}")
                    # Lemma 3(ii) sum at level r-s: sum'_k (1/k) H'_{kp^s} C(mp^{r-s}-1,k)^2 C(-mp^{r-s}-1,k-1)(-1)^k
                    Lr = m * p ** (r - s)
                    lem = 0
                    for k in range(1, Lr):
                        if k % p == 0:
                            continue
                        lem += pow(k, -1, P) * MH.H(k * p ** s) % P * (comb(Lr - 1, k) ** 2 % P) % P * ((-1) ** k * gbinom(-Lr - 1, k - 1) % P)
                    lem %= P
                    v = MH.val(lem)
                    T.log(f"   p={p} m={m} r={r} s={s}: v(Lemma-3(ii) sum) = {v}; printed count needs/gives r = {r} (-> stratum mod p^(2r-s)={2 * r - s}); strong count gives r+s = {r + s} (-> stratum mod p^2r={2 * r})")
                    T.check("strong count v >= r+s", v >= r + s, f"p={p} m={m} r={r} s={s}")
                    # reduced stratum equals -m p^{r-s} * lem mod p^{2r}
                    tally_valmod(T, "Beukers (13) = -m p^{r-s} (Lemma-3(ii) sum) mod p^{2r}", (strat + m * p ** (r - s) * lem) % P, 2 * r, MH, f"p={p} m={m} r={r} s={s}")

        T.summary("rereview_shifted_literature")


if __name__ == "__main__":
    main()
