# Sweep of Bala's fractional-factorial family A364172..A364184 with the unit-product machinery.
# Each a(n) = prod (a_i n)!^{e_i} * prod_t (x_t n/d_t)!/(y_t n/d_t)!   with y_t - x_t = c_t d_t;  (x n/d)!/(y n/d)! = d^{cn} / prod_{j<=cn} (x n + d j).
# Checks: (1) exact integrality n<=NMAX; (2) floor criterion: F(x) = sum e_i floor(a_i x) - sum_t floor(c_t x) >= #{t : x >= 1/y_t} on [0,1) (sufficient for q-integrality at odd primes q ∤ d_t);
#         (3) ratio tower a(N)/a(M) == 1 mod p^(3r) for p in {5,7}, r<=2, n<=2 (Theorem U prediction) and difference tower.
from fractions import Fraction
from math import factorial, floor
import sys
seqs={
 'A364172':([(6,1),(3,-1),(2,-1)],[(1,3,4)]),      # (6n)!(n/3)!/((3n)!(2n)!(4n/3)!)
 'A364173':([(9,1),(2,1),(4,-1),(3,-1),(1,-1)],[(3,2,9)]),   # (9n)!(2n)!(3n/2)!/((9n/2)!(4n)!(3n)!n!)
 'A364174':([(9,1),(5,-1),(3,-1)],[(5,2,9),(3,2,1)]),  # (9n)!(5n/2)!(3n/2)!/((5n)!(9n/2)!(3n)!(n/2)!)  -> pairs: (5/2)!/(9/2)!, (3/2)!/(1/2)! (inverted!)
 'A364175':([(6,1),(3,-1),(2,-1)],[(2,3,5)]),
 'A364176':([(15,1),(2,1),(6,-1),(5,-1),(1,-1)],[(5,2,15)]),  # (15n)!(5n/2)!(2n)!/((15n/2)!(6n)!(5n)!n!)
 'A364177':([(15,1),(2,1),(5,-1),(4,-1),(3,-1)],[(5,2,15)]),
 'A364178':([(10,1),(3,1),(6,-1),(5,-1),(1,-1)],[(1,2,3)]),
 'A364179':([(10,1),(5,-1),(4,-1)],[(1,2,3)]),
 'A364180':([(10,1),(5,-1),(2,-1)],[(1,2,7)]),
 'A364181':([(10,1),(5,-1),(2,-1)],[(3,2,9)]),
 'A364182':([(12,1),(6,-1),(4,-1)],[(1,2,5)]),
 'A364183':([(12,1),(2,1),(6,-1),(4,-1),(1,-1)],[(1,2,7)]),
 'A364184':([(12,1),(2,1),(6,-1),(4,-1),(1,-1)],[(3,2,9)]),
}
# pairs are (x, d, y) meaning (x n/d)! / (y n/d)!  ; if y < x the pair is inverted: (x n/d)!/(y n/d)! = prod_{j<= (x-y)n/d}(y n/d + j)
def val(name,n):
    ints,pairs=seqs[name]
    r=Fraction(1)
    for a,e in ints: r*=Fraction(factorial(a*n))**e if e>0 else 1/Fraction(factorial(a*n))
    for (x,d,y) in pairs:
        if y>x:
            c=(y-x)//d; den=Fraction(1)
            for j in range(1,c*n+1): den*=x*n+d*j
            r*=Fraction(d**(c*n))/den
        else:
            c=(x-y)//d; num=Fraction(1)
            for j in range(1,c*n+1): num*=y*n+d*j
            r*=num/Fraction(d**(c*n))
    return r
def vp(x,p):
    x=Fraction(x)
    if x==0: return 999
    a,b=x.numerator,x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 120
import json
oeis={}
import os
# first OEIS terms of A364172-A364184, with revision numbers: numerics/data/oeis_A364172-A364184.json
_data=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),'data','oeis_A364172-A364184.json')
for _k,_r in json.load(open(_data))['records'].items(): oeis[_k]=_r['data_first_8']
print("name     | matches OEIS data | integral n<=%d | floor criterion (odd q ∤ d) | ratio tower slack p=5,7 r<=2 n<=2 (min) | difference tower slack (min)"%NMAX)
for name,(ints,pairs) in seqs.items():
    vals=[val(name,n) for n in range(0,8)]
    match = oeis.get(name) and [int(v) if v.denominator==1 else None for v in vals]==oeis[name]
    integral=all(val(name,n).denominator==1 for n in range(0,NMAX+1))
    # floor criterion
    bal=sum(a*e for a,e in ints)-sum(((y-x)//d if y>x else -((x-y)//d)) for (x,d,y) in pairs)
    def F(x):
        s=sum(e*floor(a*x) for a,e in ints)
        for (xx,d,y) in pairs:
            c=(y-xx)//d if y>xx else -((xx-y)//d)
            s-= floor(c*x) if c>0 else -floor((-c)*x)
        return s
    def need(x):  # number of 'denominator' pairs (y > x) that can contribute eps=1 at this x
        return sum(1 for (xx,d,y) in pairs if y>xx and x>=Fraction(1,y))
    grid=sorted(set(Fraction(i,q) for q in range(1,61) for i in range(0,q)))
    viol=[x for x in grid if F(x)<need(x)]
    floor_ok = (bal==0) and not viol
    rs=[]; ds=[]
    for p in (5,7):
        for r in (1,2):
            for n in (1,2):
                N=n*p**r; M=N//p
                if 15*N>1200: continue
                aN=val(name,N); aM=val(name,M)
                if aM==0: continue
                rs.append(vp(aN/aM-1,p)-3*r); ds.append(vp(aN-aM,p)-3*r)
    print(f"{name} | {match} | {integral} | {'OK' if floor_ok else 'FAILS at x='+str(viol[:2]) if bal==0 else 'unbalanced'} | {min(rs) if rs else 'n/a'} | {min(ds) if ds else 'n/a'}")
