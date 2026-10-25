"""Elementary replacement of Amice's theorem in Lemma B (A370092). b_k(n, 2^m) = sum_j (-1)^(k-j) C(k,j) j^n (j^(2^m) - 1).
Claims tested:
 (2)  v2(b_k) >= m + 1 + v2(floor(k/2)!)            for m >= 1, n >= m+1, all k      (the paper's (2), via Amice)
 (2') v2(b_k) >= m + 2 + v2(floor(k/2)!)            for m >= 1, n >= m+2, floor(k/2) != 2  (new, elementary)
 (B)  v2(b_k) >= m + 1 + floor(k/3)                  for m >= 1, n >= m+2, all k      (Lemma B, now including m = 1)
 (F)  v2(floor(k/2)!) >= floor(k/3) - 1 for all k; >= floor(k/3) when floor(k/2) = 2."""
from math import comb, factorial
def v2(x):
    if x == 0: return 10**9
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
fails = {"2": 0, "2'": 0, "B": 0, "F": 0}; cnt = {"2": 0, "2'": 0, "B": 0}; minslack = {"2": 99, "2'": 99, "B": 99}
for k in range(0, 2001):
    a = k // 2
    if v2(factorial(a)) < k // 3 - 1 or (a == 2 and v2(factorial(a)) < k // 3): fails["F"] += 1
for m in range(1, 8):
    P = 2 ** m
    for n in range(m + 1, m + 30):
        for k in range(0, 56):
            b = sum((-1) ** (k - j) * comb(k, j) * j ** n * (j ** P - 1) for j in range(k + 1))
            vb = v2(b); vf = v2(factorial(k // 2))
            s = vb - (m + 1 + vf); cnt["2"] += 1; minslack["2"] = min(minslack["2"], s); fails["2"] += s < 0
            if n >= m + 2:
                s = vb - (m + 1 + k // 3); cnt["B"] += 1; minslack["B"] = min(minslack["B"], s); fails["B"] += s < 0
                if k // 2 != 2:
                    s = vb - (m + 2 + vf); cnt["2'"] += 1; minslack["2'"] = min(minslack["2'"], s); fails["2'"] += s < 0
print("cases", cnt, "failures", fails, "min slack", minslack)
