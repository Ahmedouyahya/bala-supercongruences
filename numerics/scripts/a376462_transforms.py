# Is A376462 a Legendre / binomial transform of a simpler sequence?  Solve triangular systems exactly.
from math import comb
from fractions import Fraction
import json, urllib.request, urllib.parse
def A108625(n,k): return sum(comb(n,i)**2*comb(n+k-i,k-i) for i in range(k+1))
def a(n): return sum(comb(n,k)**2*comb(n+k,k)*A108625(n,n-k) for k in range(n+1))
T=14; av=[a(n) for n in range(T)]
def solve(weight):  # find b with av[n] = sum_k weight(n,k) b[k]
    b=[]
    for n in range(T):
        s=av[n]-sum(weight(n,k)*b[k] for k in range(n))
        w=weight(n,n); b.append(Fraction(s,w))
    return b
cands={'Legendre C(n,k)C(n+k,k)':lambda n,k: comb(n,k)*comb(n+k,k), 'binomial C(n,k)':lambda n,k: comb(n,k), 'signed binomial (-1)^(n-k)C(n,k)':lambda n,k:(-1)**(n-k)*comb(n,k),
       'C(n,k)^2':lambda n,k: comb(n,k)**2, 'C(n,k)C(n+k,k)^2':lambda n,k: comb(n,k)*comb(n+k,k)**2, 'C(n+k,2k)':lambda n,k: comb(n+k,2*k), 'C(n+k,2k)C(2k,k)':lambda n,k: comb(n+k,2*k)*comb(2*k,k),
       'C(n,k)^2 C(n+k,k)':lambda n,k: comb(n,k)**2*comb(n+k,k), 'C(2n-k, n) C(n,k)':lambda n,k: comb(2*n-k,n)*comb(n,k)}
results={}
for name,w in cands.items():
    b=solve(w); integral=all(x.denominator==1 for x in b)
    results[name]=b
    print(f"{name:34s} integral={integral}  b[:8]={[str(x) for x in b[:8]]}")
# OEIS lookup for integral results
for name,b in results.items():
    if all(x.denominator==1 for x in b):
        q=','.join(str(int(x)) for x in b[1:8])
        try:
            url="https://oeis.org/search?"+urllib.parse.urlencode({'fmt':'json','q':q})
            d=json.loads(urllib.request.urlopen(url,timeout=30).read())
            rs=d if isinstance(d,list) else (d.get('results') or [])
            print(f"  OEIS for {name}: ", [('A%06d'%r['number'], r['name'][:70]) for r in rs[:3]] if rs else "no match")
        except Exception as e: print("  OEIS lookup failed:", e)
