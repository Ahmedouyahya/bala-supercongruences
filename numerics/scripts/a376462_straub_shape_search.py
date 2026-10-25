# Is 1/det(I - A diag(x)) for A376462 of Straub's shape  prod_j (1 - sum_{i in block j} s_i x_i) - eps * prod_i s_i x_i  (s_i = ±1)
# for some assignment of the five forms to the five variables, some sign pattern and some set partition into blocks?
from itertools import permutations, product
from collections import defaultdict
rows=[[1,1,1,0,0],[1,0,0,1,0],[1,1,0,1,0],[1,0,0,0,1],[1,0,1,0,1]]   # forms t+u+v, t+z, t+u+z, t+w, t+v+w over (t,u,v,z,w)
nv=5
def pmul(A,B):
    R=defaultdict(int)
    for ea,ca in A.items():
        for eb,cb in B.items():
            R[tuple(x+y for x,y in zip(ea,eb))]+=ca*cb
    return {e:c for e,c in R.items() if c}
def padd(A,B,s=1):
    R=defaultdict(int)
    for e,c in A.items(): R[e]+=c
    for e,c in B.items(): R[e]+=s*c
    return {e:c for e,c in R.items() if c}
def det_poly(M):  # M: 5x5 matrix of dict-polys; Leibniz expansion
    from itertools import permutations
    def sign(p):
        s=1
        for i in range(len(p)):
            for j in range(i+1,len(p)):
                if p[i]>p[j]: s=-s
        return s
    R={}
    for p in permutations(range(nv)):
        term={(0,)*nv:1}
        for i in range(nv):
            term=pmul(term,M[i][p[i]])
            if not term: break
        if term: R=padd(R,term,sign(p))
    return R
def unit(i):
    e=[0]*nv; e[i]=1; return tuple(e)
one={(0,)*nv:1}
def I_minus_AX(perm):
    M=[[{} for _ in range(nv)] for _ in range(nv)]
    for i in range(nv):
        for j in range(nv):
            entry={}
            if i==j: entry=dict(one)
            if rows[perm[i]][j]: entry=padd(entry,{unit(j):1},-1)
            M[i][j]=entry
    return M
# set partitions of 5 elements
def set_partitions(s):
    if not s: yield []; return
    first=s[0]
    for smaller in set_partitions(s[1:]):
        for i,sub in enumerate(smaller): yield smaller[:i]+[[first]+sub]+smaller[i+1:]
        yield [[first]]+smaller
parts=list(set_partitions(list(range(nv))))
def straub_poly(blocks,signs,eps):
    P=dict(one)
    for b in blocks:
        f=dict(one)
        for i in b: f=padd(f,{unit(i):signs[i]},-1)
        P=pmul(P,f)
    full={tuple([1]*nv): 1}
    s=1
    for i in range(nv): s*=signs[i]
    return padd(P,{tuple([1]*nv): s},-eps)
# precompute all Straub polys keyed by frozenset of items for O(1) lookup
targets={}
for blocks in parts:
    if max(len(b) for b in blocks)>2 or len(blocks)<2: continue   # Thm 3.2(b) hypotheses: ℓ>=2, max λ<=2
    for signs in product((1,-1),repeat=nv):
        for eps in (1,-1):
            key=frozenset(straub_poly(blocks,signs,eps).items())
            targets.setdefault(key,[]).append((blocks,signs,eps))
print("Straub-shape target polynomials (max block 2, >=2 blocks):", len(targets))
hits=[]
dets=set()
for perm in permutations(range(nv)):
    D=det_poly(I_minus_AX(perm)); key=frozenset(D.items()); dets.add(key)
    if key in targets: hits.append((perm,targets[key][:2]))
print("distinct determinants:", len(dets), "; hits:", hits if hits else "none")
# also allow sign flips applied to D (x_i -> s_i x_i) separately from the Straub side: equivalent to the signs loop above (both sides), so done.
# Report the structure of one determinant: number of monomials and degrees
D=det_poly(I_minus_AX((0,1,2,3,4)))
print("example determinant: #terms", len(D), "; max degree", max(sum(e) for e in D), "; contains degree-5 term", any(sum(e)==5 for e in D))
