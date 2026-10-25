# Paper A, Theorem 1.2(3)-(4): for non-degenerate triples (a,b,c) outside the classes of Theorem 1.2(2),
# search the smallest M with lambda_M(fbar) != 0 mod 3 (the leading digit of (A(3M)-A(M))/3^(3r-1)).
# Usage: python3 theoremF3_exceptions_search.py R C Mmax   (|a|,|b| <= R, c <= C, M <= Mmax).
# Reports triples without a witness that are not covered by Theorem 1.2(4) (the involution family),
# and any triple of Theorem 1.2(4) with a witness (there must be none).
import sys
import numpy as np, sys
from fractions import Fraction
def binser(e,s,n):
    out=np.zeros(n,dtype=np.int64); cur=Fraction(1)
    for k in range(n):
        out[k]=int(cur*(s**k))%3; cur=cur*(e-k)/(k+1)
    return out
def mul(p,q,n): return np.convolve(p,q)[:n]%3
def fbar(a,b,c,n):
    al=(a-b)%3; be=(-(a+b))%3
    inv1=np.array([1 if k%2==0 else 0 for k in range(n)]); inv2=np.array([((k//2)+1)%3 if k%2==0 else 0 for k in range(n)])
    psi=mul(np.array([0,al,be]),inv1,n); L=mul(np.array([0,al,2*be%3,al]),inv2,n); g=mul(np.array([0,(b*b-a*a)%3,(a*a+b*b)%3]),inv1,n)
    pm=psi.copy(); pm[0]=(pm[0]-c)%3
    return (L-mul(pm,g,n))%3
def good(a,b,c): return c%3==0 or (a+b-c)%3==0 or (a%3==0 and b%3==0)
def first_M(a,b,c,Mmax):
    n=c*Mmax+1; f=fbar(a,b,c,n); ph=mul(binser(a,1,n),binser(b,-1,n),n); pw=np.zeros(n,dtype=np.int64); pw[0]=1
    for M in range(1,Mmax+1):
        pw=mul(pw,ph,n)
        if int(np.dot(pw[:c*M+1],f[c*M::-1]))%3: return M
    return None

def involution_exception(a,b,c):
    return c%2==0 and ((c==a+2*b and a%3==0) or (c==2*a+b and b%3==0))
R=int(sys.argv[1]); C=int(sys.argv[2]); Mmax=int(sys.argv[3])
tested=0; unexplained=[]; predicted_but_witness=[]
for a in range(-R,R+1):
  for b in range(-R,R+1):
    for c in range(1,C+1):
      if good(a,b,c) or (a>=0 and b>=0 and a+b<c): continue
      tested+=1
      w=first_M(a,b,c,Mmax)
      if w is None and not involution_exception(a,b,c): unexplained.append((a,b,c))
      if w is not None and involution_exception(a,b,c): predicted_but_witness.append((a,b,c,w))
print("excluded non-degenerate triples tested:",tested)
print("no witness and not an involution exception:",unexplained)
print("involution exception but a witness found (would contradict the proof):",predicted_but_witness)
