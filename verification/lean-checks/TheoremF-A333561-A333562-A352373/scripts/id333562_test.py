from math import comb
def C(n,k): return comb(n,k) if 0<=k<=n else 0
bad=0
for n in range(1,40):
    for K in range(0,130):
        S=sum(C(n+j-1,j)*2**j for j in range(K+1))
        R=sum(C(n+K,K-k)*C(n+k-1,k) for k in range(K+1))
        D=sum(C(n+K-1,K-i)*C(n+i-1,i) for i in range(K+1))
        if S!=R: bad+=1
        if K>=1 and D!=2**K*C(n+K-1,K): bad+=1
for n in range(1,60):
    tgt=sum(C(n+j-1,j)*2**j for j in range(3*n+1)); rep=sum(C(4*n,3*n-k)*C(n+k-1,k) for k in range(3*n+1))
    if tgt!=rep: bad+=1
print("failures:",bad,"(S(n,K)=sum_k C(n+K,K-k)C(n+k-1,k) for n<40,K<130; D(n,K)=2^K C(n+K-1,K) for K>=1; target identity n<60)")
