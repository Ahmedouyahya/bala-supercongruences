"""Re-review, leftover checks.
 (1) Section 5 parenthetical: "the kernel Xi being symmetric in its two indices
     up to the position of delta" -- is Xi_u^{(delta)}(q,q') = Xi_u^{(delta)}(q',q)?
     (What the argument actually needs, Xi^'_u(k,j) = Xi^{(delta)}_{u-1}([k/p],[j/p]),
     is tested in rereview_shifted_towers.py.)
 (2) Lemma 3.2 cell-composition identity for carries, exhaustive small check.
Output: numerics/out/rereview_shifted_misc.txt
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rereview_shifted_common import Xi, Tally
HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(HERE, "out", "rereview_shifted_misc.txt"), "w") as out:
    T = Tally(out)
    T.log("(1) symmetry of Xi_u^{(delta)}(q,q') under q <-> q'")
    asym = 0; tot = 0; ex = None
    for p in (5, 7):
        for m in (1, 2):
            for u in (1, 2):
                L = m * p ** u
                for q in range(0, L):
                    for qq in range(0, L - q):
                        for d in (0, 1):
                            tot += 1
                            a, b = Xi(L, d, q, qq), Xi(L, d, qq, q)
                            if a != b:
                                asym += 1
                                if ex is None:
                                    ex = (p, m, u, q, qq, d, a, b)
    T.log(f"   pairs tested: {tot}; asymmetric: {asym}; first example (p,m,u,q,q',delta,Xi(q,q'),Xi(q',q)) = {ex}")
    T.check("Xi symmetric in (q,q') as the parenthetical says", asym == 0, f"{asym} of {tot} pairs are asymmetric")
    T.log("(2) carry composition: [(q mod p^t)+(q' mod p^t)+delta >= p^t] == [(q1 mod p^(t-1))+(q1' mod p^(t-1))+delta' >= p^(t-1)]")
    bad = 0
    for p in (5, 7):
        for t in (1, 2, 3):
            pt = p ** t
            for q in range(0, 2 * pt):
                for qq in range(0, 2 * pt):
                    for d in (0, 1):
                        dp = int((q % p) + (qq % p) + d >= p)
                        lhs = int((q % pt) + (qq % pt) + d >= pt)
                        rhs = int(((q // p) % p ** (t - 1)) + ((qq // p) % p ** (t - 1)) + dp >= p ** (t - 1))
                        if lhs != rhs:
                            bad += 1
    T.check("carry composition identity", bad == 0, f"{bad} violations")
    T.summary("rereview_shifted_misc")
