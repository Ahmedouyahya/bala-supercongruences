# exact check of: 2(n+K) f(K,i) - (K+1) f(K+1,i) = G(K,i+1) - G(K,i), G(K,i) = i*C(n+K,K+1-i)*C(n+i-1,i)
from math import comb
def C(a,b): return comb(a,b) if 0<=b<=a else 0
f=lambda n,K,i: C(n+K-1,K-i)*C(n+i-1,i)
G=lambda n,K,i: i*C(n+K,K+1-i)*C(n+i-1,i)
bad=0; cnt=0
for n in range(1,30):
    for K in range(0,40):
        for i in range(0,K+3):
            cnt+=1
            if 2*(n+K)*f(n,K,i)-(K+1)*f(n,K+1,i)!=G(n,K,i+1)-G(n,K,i): bad+=1
        if G(n,K,0)!=0 or G(n,K,K+2)!=0: bad+=1
print("cases",cnt,"failures",bad)
