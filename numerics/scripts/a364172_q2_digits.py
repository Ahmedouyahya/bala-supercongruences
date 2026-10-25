# A364172 at q=2:  v_2(a(n)) = n + s_2(n) - v_2(prod_{j<=n}(n+3j)),  and v_2(prod) = sum_k (floor(n/2^k) + extra_k),
# extra_k = [1 <= j0(k) <= n mod 2^k] with j0(k) ≡ -n * 3^{-1} (mod 2^k), j0 in [1,2^k].  Claim to test: sum_k extra_k <= 2 s_2(n), with equality iff ?
def s2(x): return bin(x).count('1')
def v2(x):
    v=0
    while x%2==0: x//=2; v+=1
    return v
def vprod(n):
    return sum(v2(n+3*j) for j in range(1,n+1))
bad=[]
eq=[]
for n in range(1,2001):
    E=vprod(n)-(n-s2(n))
    if E>2*s2(n): bad.append(n)
    if E==2*s2(n): eq.append(n)
print("violations of sum extra_k <= 2 s_2(n) for n<=2000:",bad)
print("equality cases (v_2(a(n))=0) up to 2000:",eq[:40])
# structural test: extra_k as function of the binary digits; print for n = 2^a and n = 2^a+2^b
def extras(n):
    out=[]
    k=1
    while 2**k<=4*n:
        q=2**k; R=n%q; j0=(-n*pow(3,-1,q))%q
        if j0==0: j0=q
        out.append(1 if 1<=j0<=R else 0); k+=1
    return out
for n in (1,2,4,8,3,5,6,7,9,12,24,48):
    print(n, bin(n), "extras:",extras(n), "sum",sum(extras(n)),"2s2",2*s2(n))
