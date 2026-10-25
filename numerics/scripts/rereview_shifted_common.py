"""Shared helpers for the independent re-review of
notes/A376462-shifted-congruence-proof.md.

Everything is exact (Fraction / Python int).  All definitions are transcribed
from the NOTE'S OWN text (sections 0-3), not from any earlier script.

Conventions (note, section 0):
  C(a,b) = a(a-1)...(a-b+1)/b!  for b >= 0, 0 for b < 0  (any integer a)
  B_t(l) = {k >= 0 : [k/p^t] = l}
  H'_n   = sum'_{lambda <= n} 1/lambda   (sum' = over indices prime to p)
  sigma_t(n) = sum'_{k in B_t(n)} 1/k
  S_d(x) = sum'_{mu <= x} mu^{-d}
"""
from fractions import Fraction
from functools import lru_cache
from math import comb

INF = 10 ** 9  # "valuation of zero"


def vp(x, p):
    """p-adic valuation of an int or Fraction; INF for 0."""
    if isinstance(x, Fraction):
        if x == 0:
            return INF
        return vp(x.numerator, p) - vp(x.denominator, p)
    if x == 0:
        return INF
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def gbinom(a, b):
    """Generalised binomial C(a,b) for integer a (any sign) and integer b."""
    if b < 0:
        return 0
    if a >= 0:
        return comb(a, b) if b <= a else 0
    # a < 0: C(a,b) = (-1)^b C(b-a-1, b)
    return (-1) ** b * comb(b - a - 1, b)


def floordiv(a, b):
    return a // b


# ---------------------------------------------------------------- harmonic
class Harm:
    """Harmonic-type sums for a fixed prime p, with caching."""

    def __init__(self, p):
        self.p = p
        self._H = [Fraction(0)]          # H'_n prefix table
        self._S2 = [Fraction(0)]         # S_2(n) prefix table

    def _extend(self, n):
        p = self.p
        while len(self._H) <= n:
            lam = len(self._H)
            if lam % p:
                self._H.append(self._H[-1] + Fraction(1, lam))
                self._S2.append(self._S2[-1] + Fraction(1, lam * lam))
            else:
                self._H.append(self._H[-1])
                self._S2.append(self._S2[-1])

    def H(self, n):
        """H'_n."""
        if n < 0:
            raise ValueError
        self._extend(n)
        return self._H[n]

    def S2(self, x):
        self._extend(x)
        return self._S2[x]

    def Sd(self, d, x):
        """S_d(x) = sum'_{mu<=x} mu^{-d}."""
        p = self.p
        if d == 1:
            return self.H(x)
        if d == 2:
            return self.S2(x)
        return sum((Fraction(1, mu ** d) for mu in range(1, x + 1) if mu % p),
                   Fraction(0))

    def sigma(self, t, l):
        """sigma_t(l) = sum'_{k in B_t(l)} 1/k."""
        p = self.p
        lo, hi = l * p ** t, (l + 1) * p ** t
        if lo == 0:
            return self.H(hi - 1)
        return self.H(hi - 1) - self.H(lo - 1)

    def block_S2(self, t, l):
        """sum'_{k in B_t(l)} k^{-2}."""
        p = self.p
        lo, hi = l * p ** t, (l + 1) * p ** t
        if lo == 0:
            return self.S2(hi - 1)
        return self.S2(hi - 1) - self.S2(lo - 1)

    def P(self, x, L):
        """P_x = prod'_{lambda<=x} (1 - L/lambda)."""
        p = self.p
        r = Fraction(1)
        for lam in range(1, x + 1):
            if lam % p:
                r *= (1 - Fraction(L, lam))
        return r

    def Pbar(self, x, L):
        """Pbar_x = prod'_{lambda<=x} (1 + L/lambda)."""
        p = self.p
        r = Fraction(1)
        for lam in range(1, x + 1):
            if lam % p:
                r *= (1 + Fraction(L, lam))
        return r


# ---------------------------------------------------------------- kernels
def Stilde(N, k, j):
    """S~(N;k,j) = C(N-1,k)^2 C(N+k-1,k) C(N-1,k+j)^2 C(N+j-1,j)."""
    return (gbinom(N - 1, k) ** 2 * gbinom(N + k - 1, k)
            * gbinom(N - 1, k + j) ** 2 * gbinom(N + j - 1, j))


def a_seq(n):
    """a(n) of A376462 as in the note."""
    return sum(comb(n, k) ** 2 * comb(n + k, k) * comb(n, k + j) ** 2 * comb(n + j, j)
               for k in range(n + 1) for j in range(n + 1 - k))


def Psi(L, n, j):
    """Psi_u(n,j) with L = L_u = m p^u."""
    return (gbinom(L - 1, n) ** 2 * (-1) ** n * gbinom(-L - 1, n)
            * gbinom(L - 1, n + j) ** 2 * (-1) ** j * gbinom(-L, j))


def Xi(L, delta, q, qp):
    """Xi_u^{(delta)}(q,q')."""
    return (gbinom(L - 1, q) ** 2 * (-1) ** q * gbinom(-L - 1, q)
            * gbinom(L - 1, q + qp + delta) ** 2 * (-1) ** qp * gbinom(-L - 1, qp))


def Xihat(L, n, j):
    """Xi^_u(n,j) (j >= 1)."""
    return (gbinom(L - 1, n) ** 2 * (-1) ** n * gbinom(-L - 1, n)
            * gbinom(L - 1, n + j) ** 2 * (-1) ** (j - 1) * gbinom(-L - 1, j - 1))


def Phi(L, k, j):
    """Phi_u(k,j) (section 5)."""
    return (gbinom(L - 1, k) ** 2 * (-1) ** k * gbinom(-L, k)
            * gbinom(L - 1, k + j) ** 2 * (-1) ** j * gbinom(-L - 1, j))


def Xihat_prime(L, k, j):
    """Xi^'_u(k,j) (section 5(i))."""
    return (gbinom(L - 1, k) ** 2 * (-1) ** (k - 1) * gbinom(-L - 1, k - 1)
            * gbinom(L - 1, k + j) ** 2 * (-1) ** j * gbinom(-L - 1, j))


def K_kernel(L, n):
    """K_u(n) = sum_j Psi_u(n,j)."""
    return sum(Psi(L, n, j) for j in range(0, max(0, L - n)))


def K_moment(L, n, t):
    """K_u^{[t]}(n) = sum_j j^t Psi_u(n,j)."""
    return sum(j ** t * Psi(L, n, j) for j in range(0, max(0, L - n)))


def Kprime_kernel(L, j):
    """K'_u(j) = sum_k Phi_u(k,j)."""
    return sum(Phi(L, k, j) for k in range(0, max(0, L - j)))


def fmt_slack(obs, claimed):
    if obs >= INF:
        return "inf"
    return str(obs - claimed)


class Tally:
    """Collect checks; each check has a name, claimed valuation, observed."""

    def __init__(self, out):
        self.out = out
        self.n_pass = 0
        self.n_fail = 0
        self.fails = []
        self.minslack = {}

    def log(self, s=""):
        print(s)
        self.out.write(s + "\n")

    def check(self, key, ok, detail=""):
        if ok:
            self.n_pass += 1
        else:
            self.n_fail += 1
            self.fails.append((key, detail))
            self.log(f"  FAIL  {key}  {detail}")

    def val(self, key, value, claimed, p, detail=""):
        """Record a valuation check v_p(value) >= claimed; track min slack."""
        v = vp(value, p)
        ok = v >= claimed
        slack = INF if v >= INF else v - claimed
        cur = self.minslack.get(key)
        if cur is None or slack < cur[0]:
            self.minslack[key] = (slack, detail, v, claimed)
        self.check(key, ok, f"v={v if v < INF else 'inf'} claimed>={claimed} {detail}")
        return v

    def summary(self, title):
        self.log("")
        self.log(f"== {title}: {self.n_pass} pass, {self.n_fail} fail ==")
        if self.minslack:
            self.log("minimal slack per item (observed - claimed valuation):")
            for k in sorted(self.minslack):
                s, d, v, c = self.minslack[k]
                ss = "inf" if s >= INF else str(s)
                self.log(f"  {k:48s} min slack {ss:>4s}   (v={v if v < INF else 'inf'}, claimed {c}) at {d}")
        if self.fails:
            self.log("failures:")
            for k, d in self.fails:
                self.log(f"  {k}: {d}")


# ---------------------------------------------------------------- modular engine
class ModHarm:
    """Harmonic-type sums computed in Z/p^E (all quantities are p-integral).
    Valuations are exact as long as they are < E; a zero residue is
    reported as valuation E (capped)."""

    def __init__(self, p, E):
        self.p = p
        self.E = E
        self.P = p ** E
        self._H = [0]
        self._S2 = [0]
        self._inv = [None, 1]

    def inv(self, x):
        return pow(x % self.P, -1, self.P)

    def _extend(self, n):
        p, P = self.p, self.P
        while len(self._H) <= n:
            lam = len(self._H)
            if lam % p:
                iv = pow(lam, -1, P)
                self._H.append((self._H[-1] + iv) % P)
                self._S2.append((self._S2[-1] + iv * iv) % P)
            else:
                self._H.append(self._H[-1])
                self._S2.append(self._S2[-1])

    def H(self, n):
        self._extend(n)
        return self._H[n]

    def S2(self, x):
        self._extend(x)
        return self._S2[x]

    def Sd(self, d, x):
        p, P = self.p, self.P
        if d == 1:
            return self.H(x)
        if d == 2:
            return self.S2(x)
        s = 0
        for mu in range(1, x + 1):
            if mu % p:
                s += pow(mu, -d, P)
        return s % P

    def sigma(self, t, l):
        p = self.p
        lo, hi = l * p ** t, (l + 1) * p ** t
        if lo == 0:
            return self.H(hi - 1)
        return (self.H(hi - 1) - self.H(lo - 1)) % self.P

    def block_S2(self, t, l):
        p = self.p
        lo, hi = l * p ** t, (l + 1) * p ** t
        if lo == 0:
            return self.S2(hi - 1)
        return (self.S2(hi - 1) - self.S2(lo - 1)) % self.P

    def frac(self, fr):
        """Residue of a p-integral Fraction / int."""
        if isinstance(fr, Fraction):
            return fr.numerator % self.P * pow(fr.denominator, -1, self.P) % self.P
        return fr % self.P

    def val(self, x):
        """valuation of residue x, capped at E."""
        x %= self.P
        if x == 0:
            return self.E
        return vp(x, self.p)


def tally_valmod(T, key, residue, claimed, MH, detail=""):
    """Valuation check in the modular engine (cap at MH.E)."""
    v = MH.val(residue)
    ok = v >= claimed
    slack = v - claimed
    cur = T.minslack.get(key)
    if cur is None or slack < cur[0]:
        T.minslack[key] = (slack, detail, v, claimed)
    T.check(key, ok, f"v={v}{'(cap)' if v >= MH.E else ''} claimed>={claimed} {detail}")
    return v
