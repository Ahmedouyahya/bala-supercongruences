# Numerical tests of the Lean lemma statements for Theorem F (TF*.lean), before proving them.
from fractions import Fraction as Fr
from math import comb, factorial
import itertools, sys

NP = NF = 0
def check(name, ok):
    global NP, NF
    if ok: NP += 1
    else:
        NF += 1; print("FAIL", name)

INF = 10**9
def vp(x, p):
    x = Fr(x)
    if x == 0: return INF
    a, b = x.numerator, x.denominator; v = 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
def vpn(n, p):
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def mul(f, g, K):
    return [sum(f[i]*g[n-i] for i in range(n+1)) for n in range(K+1)]
def pw(f, e, K):
    r = [Fr(1)] + [Fr(0)]*K
    for _ in range(e): r = mul(r, f, K)
    return r
def expS(f, K):  # Epoch's recursion: (k+1) G_{k+1} = sum_j (j+1) F_{j+1} G_{k-j}
    g = [Fr(0)]*(K+1); g[0] = Fr(1)
    for k in range(K):
        g[k+1] = sum((j+1)*f[j+1]*g[k-j] for j in range(k+1)) / (k+1)
    return g
def expand(f, t, K):
    return [f[n//t] if n % t == 0 else Fr(0) for n in range(K+1)]

def fc(a, b, j): return Fr(0) if j == 0 else Fr(a*(-1)**(j+1) - b, j)
def Fs(a, b, K): return [fc(a, b, j) for j in range(K+1)]
def Lc(p, a, b, j): return Fr(0) if j % p == 0 else fc(a, b, j)
def Ls(p, a, b, K): return [Lc(p, a, b, j) for j in range(K+1)]
def smul(c, f): return [c*x for x in f]

lp = lambda K: [Fr(0)] + [Fr((-1)**(j+1), j) for j in range(1, K+1)]
lm = lambda K: [Fr(0)] + [Fr(-1, j) for j in range(1, K+1)]
K = 25
# Step 1
check("expS lp = 1+X", expS(lp(K), K) == [Fr(1), Fr(1)] + [Fr(0)]*(K-1))
check("expS lm = 1-X", expS(lm(K), K) == [Fr(1), Fr(-1)] + [Fr(0)]*(K-1))
check("expS(-lm) = c1S", expS(smul(-1, lm(K)), K) == [Fr(1)]*(K+1))
c1S = [Fr(1)]*(K+1)
check("expS(-lp) = expand 2 c1S * (1-X)", expS(smul(-1, lp(K)), K) == mul(expand(c1S, 2, K), [Fr(1), Fr(-1)] + [Fr(0)]*(K-1), K))
for a, b in [(3, -1), (4, -1), (-1, -3), (2, 5), (-2, -7)]:
    check(f"F_eq {a},{b}", Fs(a, b, K) == [a*x + b*y for x, y in zip(lp(K), lm(K))])
# Step 2: (p:Q) F = expand p F + (p:Q) L ; Phi(pM) = expand p (Phi M) * expS((pM) L)
for p in (3, 5, 7):
    for a, b in [(3, -1), (4, -1), (-1, -3), (2, 5), (-2, -7)]:
        F = Fs(a, b, K); L = Ls(p, a, b, K)
        check(f"frob_F p={p} {a},{b}", smul(p, F) == [x + p*y for x, y in zip(expand(F, p, K), L)])
        for M in (1, 2, 3):
            KK = min(K, 3*p)
            lhs = expS(smul(p*M, Fs(a, b, KK)), KK)
            rhs = mul(expand(expS(smul(M, Fs(a, b, KK)), KK), p, KK), expS(smul(p*M, Ls(p, a, b, KK)), KK), KK)
            check(f"Phi_pM p={p} {a},{b} M={M}", lhs == rhs)
# Step 3: A(pM) - A(M) = sum_{w<cM} coeff (cM*p - p*w) E * coeff w (Phi M)
def A(a, b, c, N):
    KK = c*N
    return expS(smul(N, Fs(a, b, KK)), KK)[KK]
for p in (5, 7):
    for a, b, c in [(3, -1, 2), (-1, -3, 1), (2, 3, 1)]:
        for M in (1, 2):
            KK = c*M*p
            E = expS(smul(p*M, Ls(p, a, b, KK)), KK)
            PhiM = expS(smul(M, Fs(a, b, KK)), KK)
            rhs = sum(E[c*M*p - p*w]*PhiM[w] for w in range(c*M))
            check(f"A_pM_sub p={p} {a},{b},{c} M={M}", A(a, b, c, p*M) - A(a, b, c, M) == rhs)
# Step 4: h i = [p∤i]/i ; alt_sum; H_bound; Hpm_bound
for p in (5, 7, 11):
    h = lambda i: Fr(0) if i % p == 0 else Fr(1, i)
    for m in range(0, 60):
        lhs = sum((-1)**(i+1)*h(i) for i in range(2*m))
        rhs = sum(h(i) for i in range(2*m)) - sum(h(k) for k in range(m))
        check(f"alt_sum p={p} m={m}", lhs == rhs)
    for N in range(1, 300 if p == 5 else 150):
        H = sum(h(i) for i in range(N))
        check(f"H_bound p={p} N={N}", vp(H, p) >= 2*vpn(N, p))
        if N % p == 0 and N % 2 == 0:
            Hpm = sum((-1)**(i+1)*h(i) for i in range(N))
            check(f"Hpm_bound p={p} T={N}", vp(Hpm, p) >= 2*vpn(N, p))
# Step 5: T * coeff T (L^2) = 2*((a^2(-1)^T+b^2) H_T - a b (1+(-1)^T) Hpm_T), and V p (v_p T)
for p in (5, 7):
    h = lambda i: Fr(0) if i % p == 0 else Fr(1, i)
    for a, b in [(3, -1), (4, -1), (-1, -3), (2, 5), (1, 1), (0, 1)]:
        KK = 12*p
        L = Ls(p, a, b, KK); L2 = mul(L, L, KK)
        for T in range(p, KK+1, p):
            H = sum(h(i) for i in range(T)); Hpm = sum((-1)**(i+1)*h(i) for i in range(T))
            check(f"coeff_L_sq p={p} {a},{b} T={T}", T*L2[T] == 2*((a*a*(-1)**T + b*b)*H - a*b*(1+(-1)**T)*Hpm))
            check(f"V_coeff_L_sq p={p} {a},{b} T={T}", vp(L2[T], p) >= vpn(T, p))
            check(f"Lc pT zero", L[T] == 0)
# Step 6: eps bound with p^r | N (r>=1): V p k eps_T for k <= 2r + v_p T and k <= 3r
for p in (5, 7):
    for a, b in [(3, -1), (-1, -3), (2, 5)]:
        for N, r in [(p, 1), (2*p, 1), (p*p, 2), (p*p, 1), (3*p*p, 2)]:
            KK = 6*p
            E = expS(smul(N, Ls(p, a, b, KK)), KK)
            for T in range(p, KK+1, p):
                check(f"eps p={p} {a},{b} N={N} r={r} T={T}", vp(E[T], p) >= min(2*r + vpn(T, p), 3*r))
# Step 7: Lemma 6 (t,u version): p^(t+u) | M, not p^t | s  => V p (u+1) coeff s (phi^M), phi = expS F
for p in (5,):
    for a, b in [(3, -1), (-1, -3), (2, 5)]:
        for M in (1, 5, 10, 25, 50):
            KK = 130
            PhiM = expS(smul(M, Fs(a, b, KK)), KK)
            for t in range(0, 4):
                for u in range(0, 3):
                    if M % p**(t+u): continue
                    for s in range(KK+1):
                        if s % p**t == 0: continue
                        check(f"lemma6 p={p} {a},{b} M={M} t={t} u={u} s={s}", vp(PhiM[s], p) >= u+1)
# Integrality of Phi
for a, b in [(3, -1), (-1, -3), (2, 5), (-2, -7)]:
    for N in range(0, 5):
        check(f"int Phi {a},{b},{N}", all(x.denominator == 1 for x in expS(smul(N, Fs(a, b, K)), K)))
# Step 8: Theorem F: V p (3(1+v_p M)) (A(pM) - A(M))
for p in (5, 7):
    for a, b, c in [(3, -1, 2), (4, -1, 3), (-1, -3, 1), (2, 3, 1), (0, 0, 2), (1, 0, 1), (3, -1, 0)]:
        for M in ([1, 2, 5] if p == 5 else [1, 2]):
            d = A(a, b, c, p*M) - A(a, b, c, M)
            check(f"TheoremF p={p} {a},{b},{c} M={M}", vp(d, p) >= 3*(1 + vpn(M, p)))
# Step 9: instance identities
def a561(n): return sum(comb(3*n, 2*n-k)*comb(n+k-1, k) for k in range(2*n+1))
def a562(n): return sum(comb(n+j-1, j)*2**j for j in range(3*n+1))
def a562rep(n): return sum(comb(4*n, 3*n-k)*comb(n+k-1, k) for k in range(3*n+1))
def a373(n): return 0 if n == 0 else sum(comb(3*n-2*k-1, n-2*k)*comb(n+k-1, k) for k in range(n//2+1))
for N in range(1, 12):
    check(f"inst561 {N}", A(3, -1, 2, N) == a561(N))
    check(f"inst562 {N}", A(4, -1, 3, N) == a562(N) == a562rep(N))
    check(f"inst373 {N}", A(-1, -3, 1, N) == a373(N))
    # generic coefficient lemma: coeff K ((1+X)^m c1S^N) = sum_k C(m, K-k) C(N+k-1,k)
    for m in range(0, 8):
        for KK in range(0, 10):
            ser = mul(pw([Fr(1), Fr(1)] + [Fr(0)]*KK, m, KK), pw([Fr(1)]*(KK+1), N, KK), KK)
            check(f"coeff1pX {m},{N},{KK}", ser[KK] == sum(comb(m, KK-k)*comb(N+k-1, k) for k in range(KK+1)))
    # A352373 form: coeff N (expand 2 (c1S^N) * c1S^(2N))
    KK = N
    ser = mul(expand(pw([Fr(1)]*(KK+1), N, KK), 2, KK), pw([Fr(1)]*(KK+1), 2*N, KK), KK)
    check(f"coeff373 {N}", ser[N] == a373(N))
print("PASS", NP, "FAIL", NF)
