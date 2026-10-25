"""Re-review of notes/A376462-shifted-congruence-proof.md, part (b), sections 6 and 7
(and the theorem itself): class B and class S piece by piece.

Section 6: Sigma_B; Sigma_B = N^2 sum' Xi^_r(k,j)/(kj) mod p^{3r}; the inner
sum = 0 mod p^r (also split by top-level carry).
Section 7: Sigma_S - a(M-1) = -N T_S mod p^{3r} with termwise remainder
bounds of Step 1 (v(S~(M)) >= (r-1-a)^+ + (r-1-b)^+, v(e_2) >= 1+min(a,b),
v(S~(M) (E-1+N rho_S)) >= 3r); Step 2 (T_S = 3T_1 + T_2 mod p^{2r}, termwise
v(p k' Z S~(M)) >= 2r); Step 3 strata of T_1 (each = 0 mod p^{2r}; reduced
form; the Lemma 3.1 sum = 0 mod p^{r-sigma}); Step 4 likewise for T_2.
Theorem: a(N-1) = a(M-1) mod p^{3r} with the four class sums.

Arithmetic mod p^E (E = 3r+20) except the e_2 bound (exact Fractions, small cases).

Output: numerics/out/rereview_shifted_classSB.txt
"""
import os
import sys
import time
from math import comb
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import ModHarm, Tally, tally_valmod, vp, a_seq, Harm, INF

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_classSB.txt")

CASES = [(5, 2, 1), (5, 2, 2), (5, 3, 1), (5, 3, 2), (7, 2, 1), (7, 2, 2), (7, 3, 1), (7, 3, 2),
         (11, 2, 1), (11, 2, 2), (5, 2, 5), (5, 1, 5), (7, 1, 7), (5, 1, 1), (7, 1, 2), (13, 2, 1)]


class Level:
    def __init__(self, L, P):
        self.L, self.P = L, P
        self._c1, self._c2, self._c3 = {}, {}, {}

    def c1(self, n):
        if n < 0:
            return 0
        v = self._c1.get(n)
        if v is None:
            v = comb(self.L - 1, n) % self.P if n <= self.L - 1 else 0
            self._c1[n] = v
        return v

    def c2(self, n):
        if n < 0:
            return 0
        v = self._c2.get(n)
        if v is None:
            v = comb(self.L + n, n) % self.P
            self._c2[n] = v
        return v

    def c3(self, j):
        if j < 0:
            return 0
        v = self._c3.get(j)
        if v is None:
            v = comb(self.L + j - 1, j) % self.P if (self.L + j - 1 >= 0) else 0
            self._c3[j] = v
        return v

    def Stilde(self, k, j):
        return self.c1(k) ** 2 * self.c3(k) % self.P * self.c1(k + j) ** 2 % self.P * self.c3(j) % self.P

    def Xihat(self, n, j):
        return self.c1(n) ** 2 * self.c2(n) % self.P * self.c1(n + j) ** 2 % self.P * self.c2(j - 1) % self.P

    def G1(self, x):
        return sum(self.c1(x + j) ** 2 * self.c3(j) for j in range(0, max(0, self.L - x))) % self.P

    def G2(self, y):
        return sum(self.c1(k) ** 2 * self.c3(k) % self.P * self.c1(k + y) ** 2 for k in range(0, max(0, self.L - y))) % self.P

    def R1(self, kappa):   # R^{(u)}(kappa) = C(L-1,kappa)^2 (-1)^{kappa-1} C(-L-1,kappa-1) G_1(kappa)
        return self.c1(kappa) ** 2 * self.c2(kappa - 1) % self.P * self.G1(kappa) % self.P

    def R2(self, iota):    # (-1)^{iota-1} C(-L-1,iota-1) G_2(iota)
        return self.c2(iota - 1) * self.G2(iota) % self.P


def run_case(T, p, r, m):
    E = 3 * r + 20
    MH = ModHarm(p, E)
    P = MH.P
    N, M = m * p ** r, m * p ** (r - 1)
    tag = f"p={p} r={r} m={m}"
    T.log(f"--- case {tag}: N={N}, M={M}, E={E}")
    t0 = time.time()
    top = Level(N, P)
    lev = {u: Level(m * p ** u, P) for u in range(0, r)}
    inv = lambda x: pow(x, -1, P)

    # ---------------------------------------------------------------- four classes, theorem
    Sig = {"S": 0, "K": 0, "J": 0, "B": 0}
    for k in range(0, N):
        for j in range(0, N - k):
            cls = ("S" if (k % p == 0 and j % p == 0) else "K" if (k % p and j % p == 0)
                   else "J" if (k % p == 0 and j % p) else "B")
            Sig[cls] += top.Stilde(k, j)
    for c in Sig:
        Sig[c] %= P
    aM = a_seq(M - 1) % P
    aN_classes = sum(Sig.values()) % P
    if N <= 260:
        T.check("a(N-1) equals the four class sums (mod P)", a_seq(N - 1) % P == aN_classes, tag)
    tally_valmod(T, "THEOREM a(N-1) - a(M-1) = 0 mod p^{3r}", (aN_classes - aM) % P, 3 * r, MH, tag)
    tally_valmod(T, "(S) Sigma_S - a(M-1) = 0 mod p^{3r}", (Sig["S"] - aM) % P, 3 * r, MH, tag)
    tally_valmod(T, "(K) Sigma_K = 0 mod p^{3r}", Sig["K"], 3 * r, MH, tag)
    tally_valmod(T, "(J) Sigma_J = 0 mod p^{3r}", Sig["J"], 3 * r, MH, tag)
    tally_valmod(T, "(B) Sigma_B = 0 mod p^{3r}", Sig["B"], 3 * r, MH, tag)

    # ---------------------------------------------------------------- section 6
    inner = {0: 0, 1: 0}
    pr = p ** r
    for k in range(1, N):
        if k % p == 0:
            continue
        ik = inv(k)
        for j in range(1, N - k):
            if j % p == 0:
                continue
            xh = top.Xihat(k, j)
            c = int((k % pr) + (j % pr) >= pr)
            inner[c] += ik * inv(j) % P * xh
    inner_tot = (inner[0] + inner[1]) % P
    tally_valmod(T, "sec6 Sigma_B - N^2 sum' Xi^_r/(kj) = 0 mod p^{3r}", (Sig["B"] - N * N * inner_tot) % P, 3 * r, MH, tag)
    tally_valmod(T, "sec6 sum' Xi^_r(k,j)/(kj) = 0 mod p^r", inner_tot, r, MH, tag)
    for c in (0, 1):
        tally_valmod(T, "sec6 inner sum split by top-level carry c = 0 mod p^r", inner[c] % P, r, MH, f"{tag} c={c}")

    # ---------------------------------------------------------------- section 7
    low = Level(M, P)
    # P_x, Pbar_x prefix products mod P for L = N
    Pp = [1] * (N + 1)
    Pb = [1] * (N + 1)
    for lam in range(1, N + 1):
        if lam % p:
            il = inv(lam)
            Pp[lam] = Pp[lam - 1] * (1 - N * il) % P
            Pb[lam] = Pb[lam - 1] * (1 + N * il) % P
        else:
            Pp[lam] = Pp[lam - 1]
            Pb[lam] = Pb[lam - 1]

    T_S = 0
    T_1 = 0
    T_2 = 0
    Zpart = 0
    worst_term = None
    SigS_check = 0
    for kp in range(0, M):
        a = vp(kp, p) if kp else INF
        for jp in range(0, M - kp):
            b = vp(jp, p) if jp else INF
            st = low.Stilde(kp, jp)
            Eprod = Pp[p * kp] ** 2 * Pb[p * kp] % P * Pp[p * (kp + jp)] ** 2 % P * Pb[p * jp] % P
            SigS_check += st * Eprod
            rhoS = (MH.H(p * kp) + 2 * MH.H(p * (kp + jp)) - MH.H(p * jp)) % P
            T_S += st * rhoS
            T_1 += st * MH.H(p * kp)
            T_2 += st * MH.H(p * jp)
            # Step 1 termwise: S~(M)(E - 1 + N rho_S) = 0 mod p^{3r}
            rem = st * (Eprod - 1 + N * rhoS) % P
            tally_valmod(T, "sec7 Step1 termwise S~(M)(E-1+N rho_S) = 0 mod p^{3r}", rem, 3 * r, MH, f"{tag} k'={kp} j'={jp}")
            # v(S~(M)) >= (r-1-a)^+ + (r-1-b)^+
            if st % P:
                bound = max(r - 1 - a, 0) + max(r - 1 - b, 0)
                tally_valmod(T, "sec7 Step1 v(S~(M;k',j')) >= (r-1-a)^+ + (r-1-b)^+", st, bound, MH, f"{tag} k'={kp} j'={jp}")
            if kp >= 1 and jp >= 1:
                # Step 2 termwise: p k' Z S~(M) with Z = sum' 1/(mu(mu+pk'))
                Z = 0
                for mu in range(1, p * jp + 1):
                    if mu % p:
                        Z += inv(mu * (mu + p * kp))
                Z %= P
                tally_valmod(T, "sec7 Step2 v(Z) >= 1+b", Z, 1 + b, MH, f"{tag} k'={kp} j'={jp}")
                tally_valmod(T, "sec7 Step2 termwise v(p k' Z S~(M)) >= 2r", p * kp * Z % P * st % P, 2 * r, MH, f"{tag} k'={kp} j'={jp}")
                Zpart += st * (-2 * p * kp) % P * Z
    T_S %= P
    T_1 %= P
    T_2 %= P
    Zpart %= P
    T.check("sec7 Sigma_S = sum S~(M) E (mod P)", SigS_check % P == Sig["S"], tag)
    tally_valmod(T, "sec7 Step1 Sigma_S - a(M-1) + N T_S = 0 mod p^{3r}", (Sig["S"] - aM + N * T_S) % P, 3 * r, MH, tag)
    tally_valmod(T, "sec7 T_S = 0 mod p^{2r}", T_S, 2 * r, MH, tag)
    T.check("sec7 Step2 exact: T_S = 3T_1 + T_2 + Zpart (mod P)", (T_S - 3 * T_1 - T_2 - Zpart) % P == 0, tag)
    tally_valmod(T, "sec7 Step2 T_S - 3T_1 - T_2 = 0 mod p^{2r}", (T_S - 3 * T_1 - T_2) % P, 2 * r, MH, tag)
    tally_valmod(T, "sec7 Step3 T_1 = 0 mod p^{2r}", T_1, 2 * r, MH, tag)
    tally_valmod(T, "sec7 Step4 T_2 = 0 mod p^{2r}", T_2, 2 * r, MH, tag)

    # strata of T_1 and T_2
    for sig in range(1, r + 1):
        strat1 = 0
        strat2 = 0
        for kp in range(1, M):
            if vp(p * kp, p) != sig:
                continue
            strat1 += MH.H(p * kp) * low.c1(kp) ** 2 % P * low.c3(kp) % P * low.G1(kp)
            strat2 += MH.H(p * kp) * low.c3(kp) % P * low.G2(kp)
        strat1 %= P
        strat2 %= P
        tally_valmod(T, "sec7 Step3 stratum of T_1 = 0 mod p^{2r}", strat1, 2 * r, MH, f"{tag} sigma={sig}")
        tally_valmod(T, "sec7 Step4 stratum of T_2 = 0 mod p^{2r}", strat2, 2 * r, MH, f"{tag} sigma={sig}")
        if sig <= r - 1:
            u = r - sig
            lu = lev[u]
            red1 = 0
            red2 = 0
            lem1 = 0
            lem2 = 0
            for kappa in range(1, m * p ** u):
                if kappa % p == 0:
                    continue
                w = inv(kappa) * MH.H(p ** sig * kappa) % P
                red1 += w * lu.R1(kappa)
                red2 += w * lu.R2(kappa)
            red1 = m * p ** u * red1 % P
            red2 = m * p ** u * red2 % P
            tally_valmod(T, "sec7 Step3 stratum - reduced form = 0 mod p^{2r}", (strat1 - red1) % P, 2 * r, MH, f"{tag} sigma={sig}")
            tally_valmod(T, "sec7 Step4 stratum - reduced form = 0 mod p^{2r}", (strat2 - red2) % P, 2 * r, MH, f"{tag} sigma={sig}")
            # Lemma 3.1 output: sum' (1/kappa) H'_{p^sigma kappa} R^{(u)}(kappa) = 0 mod p^{2 sigma + u}
            s1 = sum(inv(k) * MH.H(p ** sig * k) % P * lu.R1(k) for k in range(1, m * p ** u) if k % p) % P
            s2 = sum(inv(k) * MH.H(p ** sig * k) % P * lu.R2(k) for k in range(1, m * p ** u) if k % p) % P
            tally_valmod(T, "sec7 Step3 Lemma-3.1 sum = 0 mod p^{2sigma+(r-sigma)}", s1, 2 * sig + u, MH, f"{tag} sigma={sig}")
            tally_valmod(T, "sec7 Step4 Lemma-3.1 sum = 0 mod p^{2sigma+(r-sigma)}", s2, 2 * sig + u, MH, f"{tag} sigma={sig}")
            # the a_kappa integrality and block sums (Lemma 2.6 with s = sigma) at level t
            for t in range(0, u + 1):
                for i in range(0, m * p ** (u - t)):
                    bs = sum(inv(k) * MH.H(p ** sig * k) for k in range(i * p ** t, (i + 1) * p ** t) if k % p) % P
                    tally_valmod(T, "sec7 Step3 block sums of a_kappa = 0 mod p^{t+2sigma}", bs, t + 2 * sig, MH, f"{tag} sigma={sig} t={t} i={i}")
    T.log(f"    ({time.time() - t0:.1f}s)")


def e2_bound_check(T):
    """Step 1: v(e_2) >= 1 + min(a,b) exactly (Fractions, small cases)."""
    T.log("sec7 Step1: v(e_2) >= 1 + min(a,b) (exact expansion of E in powers of N)")
    for p in (5, 7):
        Hm = Harm(p)
        for (m, r) in ((1, 1), (2, 1), (1, 2), (3, 1)):
            N, M = m * p ** r, m * p ** (r - 1)
            if N > 60:
                continue
            for kp in range(0, M):
                for jp in range(0, M - kp):
                    if kp == 0 and jp == 0:
                        continue
                    # expand E as polynomial in L via explicit product
                    poly = [Fraction(1)]
                    for (x, sign, mult) in ((p * kp, -1, 2), (p * kp, 1, 1), (p * (kp + jp), -1, 2), (p * jp, 1, 1)):
                        for lam in range(1, x + 1):
                            if lam % p:
                                f = [Fraction(1), Fraction(sign, lam)]
                                new = [Fraction(0)] * (len(poly) + 1)
                                for i, c in enumerate(poly):
                                    new[i] += c * f[0]
                                    new[i + 1] += c * f[1]
                                poly = new
                    e2 = poly[2] if len(poly) > 2 else Fraction(0)
                    e1 = poly[1] if len(poly) > 1 else Fraction(0)
                    a = vp(kp, p) if kp else INF
                    b = vp(jp, p) if jp else INF
                    T.val("sec7 Step1 v(e_2) >= 1+min(a,b)", e2, 1 + min(a, b), p, f"p={p} N={N} k'={kp} j'={jp}")
                    T.val("sec7 Step1 v(rho_S) >= 2+2min(a,b)", e1, 2 + 2 * min(a, b), p, f"p={p} N={N} k'={kp} j'={jp}")
                    for d in range(3, len(poly)):
                        T.val("sec7 Step1 e_d integral (d>=3)", poly[d], 0, p, f"p={p} N={N} k'={kp} j'={jp} d={d}")


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (b): class B (section 6), class S (section 7), and the theorem")
        for (p, r, m) in CASES:
            run_case(T, p, r, m)
        e2_bound_check(T)
        T.summary("rereview_shifted_classSB")


if __name__ == "__main__":
    main()
