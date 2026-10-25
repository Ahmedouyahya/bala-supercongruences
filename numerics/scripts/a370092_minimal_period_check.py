# Paper A, Proposition 7.4 (minimal period of A370092 modulo 2^alpha): direct check of
# v2(a(n+2^m)-a(n)) = m+1 for odd n >= m+7 (and >= m+2 for even n), and the finite check
# of the proof (the exceptional sum W(n,m) is 2-integral for odd n; m <= 4, n mod 8 suffice).
from fractions import Fraction as Fr
from math import comb
def v2(x):
    if x==0: return 10**9
    c=0
    while x%2==0: x//=2; c+=1
    return c
# a(n) from the defining recurrence of A370092
N=420
a=[1]
for n in range(1,N):
    s=Fr((-1)**n)+Fr(1,2)*sum((1-(-1)**j-(-2)**j)*comb(n,j)*a[n-j] for j in range(1,n+1))
    assert s.denominator==1; a.append(int(s))
print("first terms",a[:10])
viol=[]
for m in range(1,8):
    for n in range(m+7, N-2**m):
        d=v2(a[n+2**m]-a[n])
        if n%2==1 and d!=m+1: viol.append(("odd",m,n,d))
        if n%2==0 and d<m+2: viol.append(("even",m,n,d))
print("violations of: odd n>=m+7 -> v2=m+1 ; even n -> v2>=m+2 :",viol[:10],len(viol))
# smallest n from which odd-n statement holds, for curiosity
for m in range(1,6):
    bad=[n for n in range(1,60) if n%2==1 and v2(a[n+2**m]-a[n])!=m+1]
    print("m",m,"odd n failing (n<60):",bad)
# finite check used in the proof: W(n,m) 2-integral for odd n, m in 1..4, n mod 8
g=[Fr(1),Fr(1),Fr(1)]
for k in range(3,20): g.append(g[k-2]+g[k-3]/2)
E=[4,6,7,9,10,12,13,14,15]
def vq(x):
    x=Fr(x); 
    if x==0: return 10**9
    return v2(x.numerator)-v2(x.denominator)
res=[]
for m in range(1,5):
    for n0 in (1,3,5,7):
        n=n0+8*(m+7)  # representative >= m+7 in the residue class
        W=sum(g[k]*sum((-1)**(k-j)*comb(k,j)*j**n*Fr(j**(2**m)-1,2**(m+2)) for j in range(1,k+1,2)) for k in E)
        res.append((m,n0,vq(W)>=0))
print("finite check W in Z_2 (m, n mod 8, ok):",res, all(r[2] for r in res))
