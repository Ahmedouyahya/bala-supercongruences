# Fit a linear recurrence with polynomial coefficients for A376462 (order d, degree g): sum_{i=0}^{d} P_i(n) a(n+i) = 0.
from math import comb
from fractions import Fraction
from sympy import Matrix, symbols, factor, Rational, nsimplify
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
av=[a(n) for n in range(0,46)]
def fit(d,g):
    rows=[]
    for n in range(0,len(av)-d):
        rows.append([Fraction(n**e)*av[n+i] for i in range(d+1) for e in range(g+1)])
    M=Matrix(rows)
    ns=M.nullspace()
    return ns
for d in (2,3):
    for g in range(2,9):
        ns=fit(d,g)
        if ns:
            v=ns[0]; den=1
            from math import lcm
            for x in v:
                den=lcm(den, Rational(x).q)
            v=[Rational(x)*den for x in v]
            n=symbols('n')
            polys=[factor(sum(v[i*(g+1)+e]*n**e for e in range(g+1))) for i in range(d+1)]
            print(f"order {d}, degree {g}: nullspace dim {len(ns)}; recurrence coefficients P_i(n):")
            for i,P in enumerate(polys): print(f"   P_{i} =", P)
            break
    else:
        print(f"order {d}: no recurrence with degree <= 8 found from 46 terms")
        continue
    break
