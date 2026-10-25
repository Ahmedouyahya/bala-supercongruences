"""Re-review of notes/A376462-shifted-congruence-proof.md, part (b), section 2:
Lemmas 2.1 - 2.7, each recomputed from the note's own definitions, at the
claimed modulus, with slack recorded.  Also the internal pieces of the
proofs of 2.5 (base block first/second sum, s=0 branch, general-block
pieces) and of 2.6.

Arithmetic in Z/p^E, E = 30 (all quantities are p-integral); valuations
are exact below E.

Output: numerics/out/rereview_shifted_harmonic.txt
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import ModHarm, Tally, tally_valmod, vp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_harmonic.txt")
E = 30


def e_of(d, p):
    if d % (p - 1):
        return 0
    return 1 + vp(d, p)


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (b), section 2: harmonic block lemmas (mod p^E engine, E=30)")

        # ---------------------------------------------------- Lemma 2.1
        T.log("Lemma 2.1: sum_{u in (Z/p^v)^x} u^{-d} = 0 mod p^{v-e(d)}; S_d(p^v y); block sums of mu^{-2}")
        for p in (5, 7, 11):
            MH = ModHarm(p, E)
            for v in (1, 2, 3):
                if p ** v > 1400:
                    continue
                for d in range(1, 2 * (p - 1) + 3):
                    s = 0
                    for u in range(1, p ** v):
                        if u % p:
                            s += pow(u, -d, MH.P)
                    s %= MH.P
                    cl = max(v - e_of(d, p), 0)
                    tally_valmod(T, f"L2.1 unit-group power sum d={'(p-1)|d' if d % (p-1) == 0 else 'generic'}", s, cl, MH,
                                 f"p={p} v={v} d={d} e(d)={e_of(d, p)}")
                    for y in (1, 2, 3):
                        x = p ** v * y
                        if x > 5000:
                            continue
                        tally_valmod(T, "L2.1 S_d(p^v y) = 0 mod p^{v-e(d)}", MH.Sd(d, x), cl, MH, f"p={p} v={v} y={y} d={d}")
                for l in range(0, 4):
                    tally_valmod(T, "L2.1 block sum mu^{-2} over B_v(l) = 0 mod p^v", MH.block_S2(v, l), v, MH, f"p={p} v={v} l={l}")

        # ---------------------------------------------------- Lemma 2.2
        T.log("Lemma 2.2: sigma_t(l) = 0 mod p^{2t}; H'_{p^v y} = 0 mod p^{2v}")
        for p in (5, 7, 11, 13):
            MH = ModHarm(p, E)
            for t in (0, 1, 2, 3):
                for l in range(0, 6):
                    if (l + 1) * p ** t > 12000:
                        continue
                    tally_valmod(T, "L2.2 sigma_t(l) = 0 mod p^{2t}", MH.sigma(t, l), 2 * t, MH, f"p={p} t={t} l={l}")
            for v in (1, 2, 3):
                for y in (1, 2, 3, 5):
                    if p ** v * y > 12000:
                        continue
                    tally_valmod(T, "L2.2 H'_{p^v y} = 0 mod p^{2v}", MH.H(p ** v * y), 2 * v, MH, f"p={p} v={v} y={y}")

        # ---------------------------------------------------- Lemma 2.3
        T.log("Lemma 2.3: reflection; H'_{p^t-1-n} - H'_n = -p^t sum'_{n<mu<p^t} mu^{-2} mod p^{2t}; second claim mod p^{t+2s}")
        for p in (5, 7, 11):
            MH = ModHarm(p, E)
            for t in (1, 2, 3):
                pt = p ** t
                if pt > 1400:
                    continue
                for n in range(0, pt):
                    tail = (MH.S2(pt - 1) - MH.S2(n)) % MH.P
                    lhs = (MH.H(pt - 1 - n) - MH.H(n) + pt * tail) % MH.P
                    tally_valmod(T, "L2.3 first claim mod p^{2t}", lhs, 2 * t, MH, f"p={p} t={t} n={n}")
                    tally_valmod(T, "L2.3 weak form H'_{p^t-1-n} = H'_n mod p^t", (MH.H(pt - 1 - n) - MH.H(n)) % MH.P, t, MH, f"p={p} t={t} n={n}")
                for s in (1, 2):
                    if p ** (t + s) * 1 > 20000:
                        continue
                    for k in range(0, pt + 1):
                        lhs = (MH.H((pt - k) * p ** s) - MH.H(k * p ** s)) % MH.P
                        tally_valmod(T, "L2.3 second claim mod p^{t+2s}", lhs, t + 2 * s, MH, f"p={p} t={t} s={s} k={k}")

        # ---------------------------------------------------- Lemma 2.4
        T.log("Lemma 2.4: block shift")
        for p in (5, 7):
            MH = ModHarm(p, E)
            for t in (1, 2):
                pt = p ** t
                for i in (0, 1, 2, 3, p):
                    for nbar in range(0, pt):
                        n = i * pt + nbar
                        tally_valmod(T, "L2.4 H'_n = H'_{ip^t} + H'_{nbar} mod p^t", (MH.H(n) - MH.H(i * pt) - MH.H(nbar)) % MH.P, t, MH, f"p={p} t={t} i={i} nbar={nbar}")
                    for lam in range(1, pt):
                        if lam % p:
                            for d in (1, 2, 3):
                                tally_valmod(T, "L2.4 1/(ip^t+lam)^d = lam^{-d} mod p^t", (pow(i * pt + lam, -d, MH.P) - pow(lam, -d, MH.P)) % MH.P, t, MH, f"p={p} t={t} i={i} lam={lam} d={d}")

        # ---------------------------------------------------- Lemma 2.5
        T.log("Lemma 2.5: sum_{n in B_t(i)} sigma_s(n) H'_n = 0 mod p^{t+2s}  (and the pieces of its proof)")
        for p in (5, 7, 11):
            MH = ModHarm(p, E)
            P = MH.P
            for s in (0, 1, 2, 3):
                for t in (0, 1, 2, 3):
                    tp = t + s
                    if p ** tp > 20000 or (p == 11 and tp > 3):
                        continue
                    blocks = [0, 1, 2, 3, p, p + 1, 2 * p + 1]
                    for i in blocks:
                        if (i + 1) * p ** tp > 60000:
                            continue
                        tot = 0
                        for n in range(i * p ** t, (i + 1) * p ** t):
                            tot += MH.sigma(s, n) * MH.H(n)
                        tot %= P
                        tally_valmod(T, f"L2.5 main claim s={s}", tot, t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                        # interchanged form
                        tot2 = 0
                        for k in range(i * p ** tp, (i + 1) * p ** tp):
                            if k % p:
                                tot2 += pow(k, -1, P) * MH.H(k // p ** s)
                        T.check("L2.5 interchange identity", tot2 % P == tot, f"p={p} s={s} t={t} i={i}")
                    # proof pieces, base block i = 0, t >= 1
                    if t >= 1:
                        ptp = p ** tp
                        pt = p ** t
                        if s >= 1:
                            first = 0
                            second = 0
                            for k in range(1, ptp):
                                if k % p == 0:
                                    continue
                                nk = k // p ** s
                                first += (pow(k, -1, P) + pow(ptp - k, -1, P)) * MH.H(nk)
                                second += pow(ptp - k, -1, P) * (MH.H(pt - 1 - nk) - MH.H(nk))
                                T.check("L2.5 involution floor identity", (ptp - k) // p ** s == pt - 1 - nk, f"p={p} s={s} t={t} k={k}")
                            tally_valmod(T, "L2.5 proof base: first sum mod p^{t+2s}", first % P, t + 2 * s, MH, f"p={p} s={s} t={t}")
                            tally_valmod(T, "L2.5 proof base: second sum mod p^{t+2s}", second % P, t + 2 * s, MH, f"p={p} s={s} t={t}")
                            # sum'_{k<p^{t'}} k^{-2} H'_{n(k)} = 0 mod p^s
                            w = 0
                            for k in range(1, ptp):
                                if k % p:
                                    w += pow(k, -2, P) * MH.H(k // p ** s)
                            tally_valmod(T, "L2.5 proof base: sum k^-2 H'_{n(k)} mod p^s", w % P, s, MH, f"p={p} s={s} t={t}")
                        else:
                            first = second = third = 0
                            for k in range(1, pt):
                                if k % p == 0:
                                    continue
                                first += pt * pow(k * (pt - k), -1, P) * MH.H(k)
                                second += pow(pt - k, -1, P) * (MH.H(pt - 1 - k) - MH.H(k))
                                third += pow(pt - k, -2, P)
                                T.check("L2.5 s=0: H'_{p^t-k} = H'_{p^t-1-k} + 1/(p^t-k)", (MH.H(pt - k) - MH.H(pt - 1 - k) - pow(pt - k, -1, P)) % P == 0, f"p={p} t={t} k={k}")
                            tally_valmod(T, "L2.5 proof s=0: first sum mod p^t", first % P, t, MH, f"p={p} t={t}")
                            tally_valmod(T, "L2.5 proof s=0: second sum mod p^t", second % P, t, MH, f"p={p} t={t}")
                            tally_valmod(T, "L2.5 proof s=0: third sum mod p^t", third % P, t, MH, f"p={p} t={t}")
                            tot0 = 0
                            for k in range(1, pt):
                                if k % p:
                                    tot0 += pow(k, -1, P) * MH.H(k)
                            T.check("L2.5 s=0: 2 Sigma(0) = first+second+third", (2 * tot0 - first - second - third) % P == 0, f"p={p} t={t}")
                    # proof pieces, general block i >= 1, t >= 1: four pieces
                    if t >= 1:
                        for i in (1, 2, p):
                            if (i + 1) * p ** tp > 60000:
                                continue
                            pt = p ** t
                            piece1 = MH.H(i * pt) * MH.sigma(tp, i) % P
                            piece2 = 0
                            piece3 = 0
                            piece4 = 0
                            piece2b = 0  # -i p^{t'} sum tau_s(nbar) H'_nbar
                            for nbar in range(0, pt):
                                n = i * pt + nbar
                                sg = MH.sigma(s, n)
                                piece2 += sg * MH.H(nbar)
                                piece3 += -i * pt * sg * MH.S2(nbar)
                                eta = (MH.H(n) - MH.H(i * pt) - MH.H(nbar) + i * pt * MH.S2(nbar)) % P
                                piece4 += sg * eta
                                piece2b += MH.block_S2(s, nbar) * MH.H(nbar)
                            tally_valmod(T, "L2.5 general: piece1 H'_{ip^t} sigma_{t'}(i) mod p^{2t+2t'}", piece1, 2 * t + 2 * tp, MH, f"p={p} s={s} t={t} i={i}")
                            tally_valmod(T, "L2.5 general: piece2 sum sigma_s(ip^t+nbar) H'_nbar mod p^{t+2s}", piece2 % P, t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                            tally_valmod(T, "L2.5 general: p^{t'} sum tau_s H'_nbar mod p^{t+2s}", (p ** tp * piece2b) % P, t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                            tally_valmod(T, "L2.5 general: piece3 mod p^{t+2s}", piece3 % P, t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                            tally_valmod(T, "L2.5 general: piece4 (p^{2t} eta part) mod p^{2t+2s}", piece4 % P, 2 * t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                            tot = 0
                            for n in range(i * pt, (i + 1) * pt):
                                tot += MH.sigma(s, n) * MH.H(n)
                            T.check("L2.5 general: pieces sum to Sigma(i)", (piece1 + piece2 + piece3 + piece4 - tot) % P == 0, f"p={p} s={s} t={t} i={i}")

        # ---------------------------------------------------- Lemma 2.6
        T.log("Lemma 2.6: sum'_{k in B_t(i)} (1/k) H'_{k p^s} = 0 mod p^{t+2s}")
        for p in (5, 7, 11, 13):
            MH = ModHarm(p, E)
            P = MH.P
            for s in (0, 1, 2, 3):
                for t in (0, 1, 2, 3):
                    if p ** (t + s) > 20000 or (p >= 11 and t + s > 3):
                        continue
                    for i in (0, 1, 2, 3, p, p + 1, 2 * p + 1):
                        if (i + 1) * p ** (t + s) > 60000:
                            continue
                        tot = 0
                        for k in range(i * p ** t, (i + 1) * p ** t):
                            if k % p:
                                tot += pow(k, -1, P) * MH.H(k * p ** s)
                        tally_valmod(T, f"L2.6 s={s} (claimed p^(t+2s))", tot % P, t + 2 * s, MH, f"p={p} s={s} t={t} i={i}")
                        if s >= 1:
                            tally_valmod(T, f"L2.6 s={s} vs Beukers' weaker p^(t+s)", tot % P, t + s, MH, f"p={p} s={s} t={t} i={i}")
                    # base block proof pieces (s>=1, t>=1)
                    if s >= 1 and t >= 1:
                        pt = p ** t
                        first = second = 0
                        for k in range(1, pt):
                            if k % p == 0:
                                continue
                            first += pt * pow(k * (pt - k), -1, P) * MH.H(k * p ** s)
                            second += pow(pt - k, -1, P) * (MH.H((pt - k) * p ** s) - MH.H(k * p ** s))
                        tally_valmod(T, "L2.6 proof base: first sum mod p^{t+2s}", first % P, t + 2 * s, MH, f"p={p} s={s} t={t}")
                        tally_valmod(T, "L2.6 proof base: second sum mod p^{t+2s}", second % P, t + 2 * s, MH, f"p={p} s={s} t={t}")

        # ---------------------------------------------------- Lemma 2.7
        T.log("Lemma 2.7 (Y),(B): carry-restricted cell sums")
        for p in (5, 7, 11):
            MH = ModHarm(p, E)
            P = MH.P
            for t in (1, 2, 3):
                if p ** t > 130:
                    continue
                pt = p ** t
                for i in (0, 1, 2, p):
                    for ip in (0, 1, 2, p):
                        if max(i, ip) == p and t >= 2 and p >= 7:
                            continue
                        for c in (0, 1):
                            cellY = {sp: 0 for sp in (0, 1, 2)}
                            cellB = 0
                            size = 0
                            for n in range(i * pt, (i + 1) * pt):
                                nbar = n % pt
                                sig = {sp: MH.sigma(sp, n) for sp in (0, 1, 2)}
                                for j in range(ip * pt, (ip + 1) * pt):
                                    if j % p == 0:
                                        continue
                                    jbar = j % pt
                                    if int(nbar + jbar >= pt) != c:
                                        continue
                                    size += 1
                                    ij = pow(j, -1, P)
                                    for sp in (0, 1, 2):
                                        cellY[sp] += sig[sp] * ij
                                    if n % p:
                                        cellB += pow(n, -1, P) * ij
                            for sp in (0, 1, 2):
                                tally_valmod(T, f"L2.7(Y) s'={sp} mod p^(2s'+t)", cellY[sp] % P, 2 * sp + t, MH, f"p={p} t={t} i={i} i'={ip} c={c} cellsize={size}")
                            tally_valmod(T, "L2.7(B) mod p^t", cellB % P, t, MH, f"p={p} t={t} i={i} i'={ip} c={c}")

        T.summary("rereview_shifted_harmonic")


if __name__ == "__main__":
    main()
