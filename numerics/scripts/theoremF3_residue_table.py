# Theorem 1.2(3) of Paper A: for each residue class (a,b,c) mod 3, the constants K in F_3 with
# Lbar - (psibar - c) gbar = K (psibar - c). Prints "a b c [K...]"; an empty list means no such K.
# For (a,b,c) mod 3: is  f = Lbar - (psibar - c) gbar  a constant multiple K*(psibar - c) in F_3((y))?
# Work with numerators over the common denominator (1-y^2)^2, polynomials over F_3 (coefficient lists).
def pmul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]=(r[i+j]+x*y)%3
    return r
def padd(p,q,s=1):
    n=max(len(p),len(q)); p=p+[0]*(n-len(p)); q=q+[0]*(n-len(q))
    return [(x+s*y)%3 for x,y in zip(p,q)]
def norm(p):
    while p and p[-1]==0: p=p[:-1]
    return p
rows=[]
for a in range(3):
  for b in range(3):
    al=(a-b)%3; be=(-(a+b))%3
    for c in range(3):
      Lnum=[0,al,(2*be)%3,al]                    # y(al+2be y+al y^2)
      psimc=padd([0,al,be],pmul([c],[1,0,-1%3]),-1)   # y(al+be y) - c(1-y^2)
      gnum=[0,(b*b-a*a)%3,(a*a+b*b)%3]            # y[(b^2-a^2)+(a^2+b^2)y]
      f=padd(Lnum,pmul(psimc,gnum),-1)            # numerator of f over (1-y^2)^2
      base=pmul(psimc,[1,0,2])                    # numerator of (psi-c) over (1-y^2)^2
      Ks=[K for K in range(3) if norm(padd(f,pmul([K],base),-1))==[]]
      rows.append(((a,b,c),Ks))
for (a,b,c),Ks in rows: print(a,b,c,Ks)
