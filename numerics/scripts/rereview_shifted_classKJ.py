"""Re-review of notes/A376462-shifted-congruence-proof.md, part (b), sections 4 and 5:
class K and class J, every displayed piece recomputed from the note's own
definitions at the claimed modulus, with slack.

Pieces (section 4):  Sigma_K; (4.1); (4.a); (4.2); X^, X^_1, X^_2, X^_3 and
the t-th terms of the X^_3 series; A_s (0<=s<=r-1); the step
A_{s+1} = A_s - m p^{s+1} X_s + m p^{s+1} Y_s; X_s, X_{s,1}, X_{s,2}, X_{s,3}
(and series terms), Y_s (also split by carry c).
Section 5: the same with (Phi, harmonic index j, kernel index k) and
rho' = -H'_j + H'_{pk1} + 2H'_{j+pk1}.

Arithmetic mod p^E (E = 3r+20); all quantities are p-integral.

Output: numerics/out/rereview_shifted_classKJ.txt
"""
import os
import sys
import time
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import ModHarm, Tally, tally_valmod

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "rereview_shifted_classKJ.txt")

CASES = [(5, 2, 1), (5, 2, 2), (5, 3, 1), (5, 3, 2), (7, 2, 1), (7, 2, 2), (7, 3, 1), (7, 3, 2),
         (11, 2, 1), (11, 2, 2), (5, 2, 5), (5, 1, 5), (7, 1, 7), (5, 1, 1), (7, 1, 2)]


class Level:
    """Residues mod P of the binomial factors at level L = m p^u."""

    def __init__(self, L, P):
        self.L, self.P = L, P
        self._c1, self._c2, self._c3 = {}, {}, {}

    def c1(self, n):  # C(L-1, n)
        if n < 0:
            return 0
        v = self._c1.get(n)
        if v is None:
            v = comb(self.L - 1, n) % self.P if n <= self.L - 1 else 0
            self._c1[n] = v
        return v

    def c2(self, n):  # (-1)^n C(-L-1, n) = C(L+n, n)
        if n < 0:
            return 0
        v = self._c2.get(n)
        if v is None:
            v = comb(self.L + n, n) % self.P
            self._c2[n] = v
        return v

    def c3(self, j):  # (-1)^j C(-L, j) = C(L+j-1, j)
        if j < 0:
            return 0
        v = self._c3.get(j)
        if v is None:
            v = comb(self.L + j - 1, j) % self.P if (self.L + j - 1 >= 0) else 0
            self._c3[j] = v
        return v

    def Psi(self, n, j):
        return self.c1(n) ** 2 * self.c2(n) % self.P * self.c1(n + j) ** 2 % self.P * self.c3(j) % self.P

    def Xihat(self, n, j):
        return self.c1(n) ** 2 * self.c2(n) % self.P * self.c1(n + j) ** 2 % self.P * self.c2(j - 1) % self.P

    def Phi(self, k, j):
        return self.c1(k) ** 2 * self.c3(k) % self.P * self.c1(k + j) ** 2 % self.P * self.c2(j) % self.P

    def Xihat_prime(self, k, j):
        return self.c1(k) ** 2 * self.c2(k - 1) % self.P * self.c1(k + j) ** 2 % self.P * self.c2(j) % self.P

    def Stilde(self, k, j):
        return self.c1(k) ** 2 * self.c3(k) % self.P * self.c1(k + j) ** 2 % self.P * self.c3(j) % self.P

    def K(self, n):
        return sum(self.Psi(n, j) for j in range(0, max(0, self.L - n))) % self.P

    def Kmom(self, n, t):
        return sum(j ** t * self.Psi(n, j) for j in range(0, max(0, self.L - n))) % self.P

    def Kp(self, j):
        return sum(self.Phi(k, j) for k in range(0, max(0, self.L - j))) % self.P

    def Kpmom(self, j, t):
        return sum(k ** t * self.Phi(k, j) for k in range(0, max(0, self.L - j))) % self.P


def run_case(T, p, r, m):
    E = 3 * r + 20
    MH = ModHarm(p, E)
    P = MH.P
    N, M = m * p ** r, m * p ** (r - 1)
    tag = f"p={p} r={r} m={m}"
    T.log(f"--- case {tag}: N={N}, M={M}, E={E}")
    t0 = time.time()
    lev = {u: Level(m * p ** u, P) for u in range(0, r + 1)}
    top = lev[r]
    inv = lambda x: pow(x, -1, P)

    # ================================================================ class K
    SigK = 0
    for k in range(1, N):
        if k % p == 0:
            continue
        for j in range(0, N - k, p):
            SigK += top.Stilde(k, j)
    SigK %= P
    tally_valmod(T, "(K) Sigma_K = 0 mod p^{3r}", SigK, 3 * r, MH, tag)

    Khat = {}
    for k in range(1, N):
        if k % p:
            Khat[k] = sum(top.Psi(k, p * j1) for j1 in range(0, (N - k) // p + 1)) % P
    S1 = sum(inv(k) * Khat[k] for k in Khat) % P            # sum' (1/k) K^_r(k)
    S2 = sum(inv(k * k) * Khat[k] for k in Khat) % P        # sum' (1/k^2) K^_r(k)
    tally_valmod(T, "(4.1) Sigma_K - [N S1 - N^2 S2] = 0 mod p^{3r}", (SigK - N * S1 + N * N * S2) % P, 3 * r, MH, tag)
    tally_valmod(T, "(4.a) sum'(1/k^2) K^_r(k) = 0 mod p^r", S2, r, MH, tag)
    tally_valmod(T, "(4.b) sum'(1/k) K^_r(k) = 0 mod p^{2r}", S1, 2 * r, MH, tag)

    # (4.2): S1 ≡ A_{r-1} - N X^  (mod p^{2r})
    def A_of(s):
        Ls = m * p ** s
        return sum(MH.sigma(r - s, n) * lev[s].K(n) for n in range(0, Ls)) % P

    A = {s: A_of(s) for s in range(0, r)}
    low = lev[r - 1]
    X1 = X2 = X3 = 0
    for k in Khat:
        npr = k // p
        ik = inv(k)
        Kq = low.K(npr)
        X1 += ik * MH.H(k) % P * Kq
        for j1 in range(0, max(0, M - npr)):
            ps = low.Psi(npr, j1)
            if ps == 0:
                continue
            X2 += ik * ps % P * MH.H(p * j1)
            X3 += ik * ps % P * MH.H(k + p * j1)
    X1 %= P
    X2 %= P
    X3 %= P
    Xhat = (X1 - X2 + 2 * X3) % P
    tally_valmod(T, "(4.2) S1 - (A_{r-1} - N X^) = 0 mod p^{2r}", (S1 - A[r - 1] + N * Xhat) % P, 2 * r, MH, tag)
    tally_valmod(T, "(4.b.1) X^ = 0 mod p^r", Xhat, r, MH, tag)
    tally_valmod(T, "(4.b.1) X^_1 = 0 mod p^r", X1, r, MH, tag)
    tally_valmod(T, "(4.b.1) X^_2 = 0 mod p^{r+1}", X2, r + 1, MH, tag)
    tally_valmod(T, "(4.b.1) X^_3 = 0 mod p^r", X3, r, MH, tag)
    # X^_3 series terms: t-th term = (-p)^t sum'_k (1/k) S_{t+1}(k) K^[t]_{r-1}(n')
    series = 0
    for t in range(0, 6):
        term = 0
        for k in Khat:
            term += inv(k) * MH.Sd(t + 1, k) % P * low.Kmom(k // p, t)
        term = (-p) ** t * term % P
        series += term
        if t == 0:
            T.check("X^_3 series t=0 term equals X^_1", term == X1, tag)
        else:
            tally_valmod(T, "X^_3 series term t>=1 = 0 mod p^{t+r-1}", term, t + r - 1, MH, f"{tag} t={t}")
    tally_valmod(T, "X^_3 = X^_2 + series (truncated at 6 terms) mod p^{r+5}", (X3 - X2 - series) % P, r + 5, MH, tag)

    # (4.b.2) induction
    for s in range(0, r):
        tally_valmod(T, "(4.b.2) A_s = 0 mod p^{2r}", A[s], 2 * r, MH, f"{tag} s={s}")
    for s in range(0, r - 1):
        sp = r - s - 1
        Ls1 = m * p ** (s + 1)
        L = Ls1
        ls, ls1 = lev[s], lev[s + 1]
        Xs1 = Xs2 = Xs3 = 0
        Ys = {0: 0, 1: 0}
        Ys_tot = 0
        for n in range(0, Ls1):
            q = n // p
            sg = MH.sigma(sp, n)
            if sg % P == 0:
                pass
            Xs1 += sg * MH.H(n) % P * ls.K(q)
            for j1 in range(0, max(0, m * p ** s - q)):
                ps = ls.Psi(q, j1)
                if ps == 0:
                    continue
                Xs2 += sg * ps % P * MH.H(p * j1)
                Xs3 += sg * ps % P * MH.H(n + p * j1)
            pt = p ** (s + 1)
            nbar = n % pt
            for j in range(1, max(0, L - n)):
                if j % p == 0:
                    continue
                xh = ls1.Xihat(n, j)
                if xh == 0:
                    continue
                val = sg * inv(j) % P * xh
                c = int(nbar + (j % pt) >= pt)
                Ys[c] += val
                Ys_tot += val
        Xs1 %= P
        Xs2 %= P
        Xs3 %= P
        Xs = (Xs1 - Xs2 + 2 * Xs3) % P
        Ys_tot %= P
        step = (A[s + 1] - A[s] + m * p ** (s + 1) * Xs - m * p ** (s + 1) * Ys_tot) % P
        tally_valmod(T, "(4.b.2) step A_{s+1} - A_s + mp^{s+1}X_s - mp^{s+1}Y_s = 0 mod p^{2r}", step, 2 * r, MH, f"{tag} s={s}")
        tally_valmod(T, "(4.b.2) X_s = 0 mod p^{2r-s-1}", Xs, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(4.b.2) X_{s,1} = 0 mod p^{2r-s-1}", Xs1, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(4.b.2) X_{s,2} = 0 mod p^{2r-s}", Xs2, 2 * r - s, MH, f"{tag} s={s}")
        tally_valmod(T, "(4.b.2) X_{s,3} = 0 mod p^{2r-s-1}", Xs3, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(4.b.2) Y_s = 0 mod p^{2r-s-1}", Ys_tot, 2 * r - s - 1, MH, f"{tag} s={s}")
        for c in (0, 1):
            tally_valmod(T, "(4.b.2) Y_s split by top-level carry c = 0 mod p^{2r-s-1}", Ys[c] % P, 2 * r - s - 1, MH, f"{tag} s={s} c={c}")
        # series terms of X_{s,3}
        for t in range(1, 5):
            term = 0
            for n in range(0, Ls1):
                term += MH.sigma(sp, n) * MH.Sd(t + 1, n) % P * ls.Kmom(n // p, t)
            term = (-p) ** t * term % P
            tally_valmod(T, "X_{s,3} series term t>=1 = 0 mod p^{t+2s'+s}", term, t + 2 * sp + s, MH, f"{tag} s={s} t={t}")

    # ================================================================ class J (mirror)
    SigJ = 0
    for k in range(0, N, p):
        for j in range(1, N - k):
            if j % p:
                SigJ += top.Stilde(k, j)
    SigJ %= P
    tally_valmod(T, "(J) Sigma_J = 0 mod p^{3r}", SigJ, 3 * r, MH, tag)
    Khatp = {}
    for j in range(1, N):
        if j % p:
            Khatp[j] = sum(top.Phi(p * k1, j) for k1 in range(0, (N - j) // p + 1)) % P
    S1p = sum(inv(j) * Khatp[j] for j in Khatp) % P
    S2p = sum(inv(j * j) * Khatp[j] for j in Khatp) % P
    tally_valmod(T, "(J) Sigma_J - [N S1' - N^2 S2'] = 0 mod p^{3r}", (SigJ - N * S1p + N * N * S2p) % P, 3 * r, MH, tag)
    tally_valmod(T, "(J) sum'(1/j^2) K^'_r(j) = 0 mod p^r", S2p, r, MH, tag)
    tally_valmod(T, "(J) sum'(1/j) K^'_r(j) = 0 mod p^{2r}", S1p, 2 * r, MH, tag)

    def Ap_of(s):
        Ls = m * p ** s
        return sum(MH.sigma(r - s, j) * lev[s].Kp(j) for j in range(0, Ls)) % P

    Ap = {s: Ap_of(s) for s in range(0, r)}
    X1p = X2p = X3p = 0
    for j in Khatp:
        q = j // p
        ij = inv(j)
        X1p += ij * MH.H(j) % P * low.Kp(q)
        for k1 in range(0, max(0, M - q)):
            ph = low.Phi(k1, q)
            if ph == 0:
                continue
            X2p += ij * ph % P * MH.H(p * k1)
            X3p += ij * ph % P * MH.H(j + p * k1)
    X1p %= P
    X2p %= P
    X3p %= P
    Xhatp = (-X1p + X2p + 2 * X3p) % P
    tally_valmod(T, "(J) S1' - (A'_{r-1} - N X^') = 0 mod p^{2r}  [rho' = -H'_j + H'_{pk1} + 2H'_{j+pk1}]", (S1p - Ap[r - 1] + N * Xhatp) % P, 2 * r, MH, tag)
    tally_valmod(T, "(J) X^' = 0 mod p^r", Xhatp, r, MH, tag)
    tally_valmod(T, "(J) X^'_1 = 0 mod p^r", X1p, r, MH, tag)
    tally_valmod(T, "(J) X^'_2 = 0 mod p^{r+1}", X2p, r + 1, MH, tag)
    tally_valmod(T, "(J) X^'_3 = 0 mod p^r", X3p, r, MH, tag)
    # with the "wrong" sign pattern (the referee's reported sign slip): would it still vanish?
    Xhatp_alt = (X1p - X2p + 2 * X3p) % P
    tally_valmod(T, "(J) [diagnostic] X^' with class-K sign pattern = 0 mod p^r", Xhatp_alt, r, MH, tag)
    for s in range(0, r):
        tally_valmod(T, "(J) A'_s = 0 mod p^{2r}", Ap[s], 2 * r, MH, f"{tag} s={s}")
    for s in range(0, r - 1):
        sp = r - s - 1
        Ls1 = m * p ** (s + 1)
        L = Ls1
        ls, ls1 = lev[s], lev[s + 1]
        Xs1 = Xs2 = Xs3 = 0
        Ys = {0: 0, 1: 0}
        Ys_tot = 0
        for j in range(0, Ls1):
            q = j // p
            sg = MH.sigma(sp, j)
            Xs1 += sg * MH.H(j) % P * ls.Kp(q)
            for k1 in range(0, max(0, m * p ** s - q)):
                ph = ls.Phi(k1, q)
                if ph == 0:
                    continue
                Xs2 += sg * ph % P * MH.H(p * k1)
                Xs3 += sg * ph % P * MH.H(j + p * k1)
            pt = p ** (s + 1)
            jbar = j % pt
            for k in range(1, max(0, L - j)):
                if k % p == 0:
                    continue
                xh = ls1.Xihat_prime(k, j)
                if xh == 0:
                    continue
                val = sg * inv(k) % P * xh
                c = int(jbar + (k % pt) >= pt)
                Ys[c] += val
                Ys_tot += val
        Xs1 %= P
        Xs2 %= P
        Xs3 %= P
        Xs = (-Xs1 + Xs2 + 2 * Xs3) % P
        Ys_tot %= P
        step = (Ap[s + 1] - Ap[s] + m * p ** (s + 1) * Xs - m * p ** (s + 1) * Ys_tot) % P
        tally_valmod(T, "(J) step A'_{s+1} - A'_s + mp^{s+1}X'_s - mp^{s+1}Y'_s = 0 mod p^{2r}", step, 2 * r, MH, f"{tag} s={s}")
        tally_valmod(T, "(J) X'_s = 0 mod p^{2r-s-1}", Xs, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(J) X'_{s,1} = 0 mod p^{2r-s-1}", Xs1, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(J) X'_{s,2} = 0 mod p^{2r-s}", Xs2, 2 * r - s, MH, f"{tag} s={s}")
        tally_valmod(T, "(J) X'_{s,3} = 0 mod p^{2r-s-1}", Xs3, 2 * r - s - 1, MH, f"{tag} s={s}")
        tally_valmod(T, "(J) Y'_s = 0 mod p^{2r-s-1}", Ys_tot, 2 * r - s - 1, MH, f"{tag} s={s}")
        for c in (0, 1):
            tally_valmod(T, "(J) Y'_s split by carry c = 0 mod p^{2r-s-1}", Ys[c] % P, 2 * r - s - 1, MH, f"{tag} s={s} c={c}")
    T.log(f"    ({time.time() - t0:.1f}s)")


def main():
    with open(OUT, "w") as out:
        T = Tally(out)
        T.log("Re-review (b): class K (section 4) and class J (section 5) piece by piece")
        for (p, r, m) in CASES:
            run_case(T, p, r, m)
        T.summary("rereview_shifted_classKJ")


if __name__ == "__main__":
    main()
