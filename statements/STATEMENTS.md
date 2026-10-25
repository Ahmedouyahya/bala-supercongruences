# F1

## A333561 — a(n) = Sum_{j = 0..2*n} binomial(n+j-1,j)*2^j.

- OEIS: https://oeis.org/A333561
- offset: 0,2
- data: 1,7,129,2815,65537,1579007,38862849,970522623,24494735361,623210135551,15956734640129,410649406472191,10612705274626049,

**Formulas:**
- Conjectural o.g.f.: 1/(1 + x) + 8*x*f'(4*x)/(2*f(4*x) - 1), where f(x) = 1 + x + 3*x^2 + 12*x^3 + 55*x^4 + ... is the o.g.f. of A001764.
- exp( Sum_{n >= 1} a(n)*x^n/n ) = 1 + 7*x + 89*x^2 + 1447*x^3 + ... appears to be the o.g.f. of A062747.
- Conjectural recurrence: n*(n - 1)*(2*n - 1)*(3098*n - 6455)*a(n) = (n - 1)*(172988*n^3 - 585840*n^2 + 550321*n - 169824)*a(n-1) - 12*(11825*n^4 - 168518*n^3 + 627675*n^2 - 853766*n + 350744)*a(n-2) - 36*(n - 3)*(3*n - 7)*(3*n - 8)*(991*n - 724)*a(n-3) with a(1) = 7, a(2) = 129, a(3) = 2815.
- From _Vaclav Kotesovec_, Mar 28 2020: (Start)
- a(n) ~ 3^(3*n + 1/2) / (4*sqrt(Pi*n)).
- Recurrence: n*(2*n - 1)*(7*n^2 - 20*n + 14)*a(n) = (364*n^4 - 1411*n^3 + 1818*n^2 - 868*n + 120)*a(n-1) + 6*(3*n - 5)*(3*n - 4)*(7*n^2 - 6*n + 1)*a(n-2). (End)
- From _Peter Bala_, Mar 05 2022: (Start)
- a(n) = Sum_{k = 0..2*n} binomial(3*n, 2*n-k)*binomial(n+k-1,k).

**Comments (conjectures and context):**
- We conjecture that this sequence satisfies the supercongruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Some examples are given below.

**Links:**

**Programs:** (PARI) a(n) = sum(j = 0, 2*n, binomial(n+j-1,j)*2^j); \\ _Michel Marcus_, Mar 28

## A333562 — a(n) = Sum_{j = 0..3*n} binomial(n+j-1,j)*2^j.

- OEIS: https://oeis.org/A333562
- offset: 0,2
- data: 1,15,769,47103,3080193,208470015,14413725697,1011196362751,71695889072129,5124481173422079,368599603785760769,2664885998

**Formulas:**
- Conjectural o.g.f.: 1/(1 + x) + 16*x*f'(8*x)/(2*f(8*x) - 1), where f(x) = 1 + x + 4*x^2 + 22*x^3 + 140*x^4 + ... is the o.g.f. of A002293.
- exp( Sum_{n >= 1} a(n)*x^n/n ) = 1 + 15*x + 497*x^2 + 22031*x^3 + ... appears to be the o.g.f. of A062752.
- a(n) ~ 2^(11*n + 3/2) / (5*sqrt(Pi*n) * 3^(3*n + 1/2)). - _Vaclav Kotesovec_, Mar 28 2020
- For n >= 1, a(n) = n*binomial(4*n, n)*Integral_{x = 1..2} x^(3*n)*(x - 1)^(n-1) dx. - _Peter Bala_, Aug 22 2026
- Recurrence: 3*n*(3*n - 2)*(3*n - 1)*(415*n^3 - 1815*n^2 + 2612*n - 1236)*a(n) = (838715*n^6 - 4931790*n^5 + 11279837*n^4 - 12621918*n^3 + 7111532*n^2 - 1846728*n + 161280)*a(n-1) + 64*(2*n - 3)*(4*n - 7)*(4*n - 5)*(415*n^3 - 570*n^2 + 227*n - 24)*a(n-2). - _Vaclav Kotesovec_, Aug 22 2026

**Comments (conjectures and context):**
- We conjecture that this sequence satisfies the congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Some examples are given below.

**Links:**

**Programs:** (PARI) a(n) = sum(j = 0, 3*n, binomial(n+j-1,j)*2^j); \\ _Michel Marcus_, Mar 28

## A352275 — a(0) = 1 and a(n) = Sum_{k = 0..2*n} n/(n + 2*k)*binomial(n + 2*k,k) for n >= 1.

- OEIS: https://oeis.org/A352275
- offset: 0,2
- data: 1,4,64,1429,35072,898129,23571781,628750217,16965558016,461752375705,12652302369439,348552604899778,9644571491252069,267

**Formulas:**
- a(n) ~ 5^(5*n + 3/2) / (19 * sqrt(Pi*n) * 2^(2*n + 1) * 3^(3*n + 1/2)). - _Vaclav Kotesovec_, Mar 15 2022

**Comments (conjectures and context):**
- The binomial coefficients A005809(n) are known to satisfy the supercongruences A005809(n*p^r) == A005809(n*p^(r-1)) (mod p^(3*r)) for primes p >= 5 and positive integers n and r (see Meštrović, equation 39). Calculation suggests that the present sequence satisfies the same congruences.
- Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for primes p >= 5 and positive integers n and r.
- Then we conjecture that each sequence u_m satisfies the above supercongruences. This is the case m = 2. See A333093 (case m = 1) and A352276 case (m = 3).

**Links:**
- Paolo Xausa, Table of n, a(n) for n = 0..674
- R. Meštrović, Wolstenholme's theorem: Its Generalizations and Extensions in the last hundred and fifty years (1862--2012), arXiv:1111.3057 [math.NT], 2011.

**Programs:** (PARI) a(n) = if (n==0, 1, sum(k=0, 2*n, binomial(n + 2*k,k)*n/(n+2*k))); \\ _Mi

# F2

## A352373 — a(n) = [x^n] ( 1/((1 - x)^2*(1 - x^2)) )^n for n >= 1.

- OEIS: https://oeis.org/A352373
- offset: 1,1
- data: 2,12,74,484,3252,22260,154352,1080612,7621526,54071512,385454940,2758690636,19810063392,142662737376,1029931873824,74514

**Formulas:**
- a(n) = Sum_{k = 0..floor(n/2)} binomial(3*n-2*k-1,n-2*k)*binomial(n+k-1,k).
- a(n) = Sum_{k = 0..n} (-1)^k*binomial(4*n-k-1,n-k)*binomial(n+k-1,k).
- a(n) = binomial(4*n-1,n)*hypergeom([n, -n], [1-4*n], -1).
- 48*n*(n-1)*(3*n-1)*(3*n-2)*(93*n^3-434*n^2+668*n-339)*a(n) = 12*(n-1)*(21762*n^6-134199*n^5+323805*n^4-386685*n^3+237728*n^2-70336*n+7680)*a(n-1) + 5*(5*n-9)*(5*n-8)*(5*n-7)*(5*n-6)*(93*n^3-155*n^2+79*n-12)*a(n-2) with a(1) = 2 and a(2) = 12.
- The o.g.f. A(x) = 2*x + 12*x^2 + 74*x^3 + ... is the diagonal of the bivariate rational function x*t/(1 - t/((1 - x)^2*(1 - x^2))) and hence is an algebraic function over Q(x) by Stanley 1999, Theorem 6.33, p. 197.
- A(x) = x*d/dx(log(F(x))), where F(x) = (1/x)*Series_Reversion( x*(1 - x)^2*(1 - x^2) ).
- a(n) ~ sqrt(4 + sqrt(6)) * (13/4 + 31*sqrt(6)/18)^n / (2*sqrt(5*Pi*n)). - _Vaclav Kotesovec_, Mar 15 2022

**Comments (conjectures and context):**
- The Gauss congruences a(n*p^k) == a(n*p^(k-1)) (mod p^k) hold for all primes p and positive integers n and k.
- Calculation suggests that, in fact, stronger congruences may hold.
- Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for all primes p >= 5 and positive integers n and k.
- Conjecture: for each r and s the above supercongruences hold for the sequence a(r,s;n) for n >= 1.

**Links:**
- Paolo Xausa, Table of n, a(n) for n = 1..1000

**Programs:** (Magma) | A352373:= func< n | (&+[(-1)^k*Binomial(4*n-k-1,n-k)*Binomial(n+k-1,k): k in [0.

## A386548 — a(n) = [x^n] ((1 - x)/(1 - x + x^2))^n.

- OEIS: https://oeis.org/A386548
- offset: 0,3
- data: 1,0,-2,-3,6,25,1,-147,-218,591,2223,-484,-14871,-18759,68353,222697,-116058,-1629671,-1656989,8275203,23266031,-20154144

**Formulas:**
- a(n) = Sum_{k = 0..floor(n/2)} binomial(-n, k)*binomial(n-k-1, n-2*k) = Sum_{k = 0
- ..floor(n/2)} (-1)^k*binomial(n+k-1, k)*binomial(n-k-1, n-2*k). Cf. A246437.
- a(n) = -n*hypergeom([n+1, 1 - (1/2)*n, 3/2 - (1/2)*n], [2, 2 - n], 4) for n >= 3.
- P-recursive: 3*n*(n - 1)*(19*n^2 - 79*n + 78)*a(n) = 2*(n - 1)*(2*n - 3)*(19*n^2 - 60*n + 36)*a(n-1) - 2*(190*n^4 - 1170*n^3 + 2519*n^2 - 2229*n + 666)*a(n-2) - 2*(n - 3)*(2*n - 3)*(19*n^2 - 41*n + 18)*a(n-3) with a(0) = 1, a(1) = 0 and a(2) = -2.
- exp( Sum_{n >= 1} a(n)*(-x)^n/n ) = 1 - x^2 + x^3 + 2*x^4 - 6*x^5 - x^6 +  ... is the g.f. of A364374.

**Comments (conjectures and context):**
- The Gauss congruences a(n*p^k) == a(n*p^(k-1)) (mod p^k) hold for all primes p and all positive integers n and k.
- Conjecture: the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for all primes p >= 5 and all positive integers n and k.

**Links:**

**Programs:** (PARI) a(n) = my(x='x+O('x^(n+1))); polcoef(((1 - x)/(1 - x + x^2))^n, n); \\ _M

# F3

## A363983 — a(n) = Sum_{k = floor((n+1)/2)..n} (-1)^(n+k)*binomial(n,k)*binomial(n+k-1,k)*binomial(2*k,n).

- OEIS: https://oeis.org/A363983
- offset: 0,2
- data: 1,2,14,128,1310,14252,161168,1872096,22179102,266766500,3247293764,39914850560,494587904720,6170138404640,77420709800000

**Formulas:**
- a(2*n) = (-1)^n*(2/3)*(3*n)!/n!^3 * hypergeom([3*n, n + 1/2, -n],[n + 1, 1/2], 1) for n >= 1.
- a(2*n+1) = 2*binomial(4*n+1, 2*n+1)*binomial(4*n+1, 2*n) * hypergeom([-n, -(2*n + 1), -(2*n + 1)/2], [-(4*n + 1), -(4*n + 1)/2], 1).
- P-recursive: 2*(n^2)*(n - 1)*(5*n^2 - 16*n + 13)*a(n) = (n - 1)*(145*n^4 - 609*n^3 + 868*n^2 - 480*n + 96)*a(n-1) - 3*(n - 2)*(3*n - 4)*(3*n - 5)*(5*n^2 - 6*n + 2)*a(n-2) with a(0) = 1 and a(1) = 2.

**Comments (conjectures and context):**
- The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences.

**Links:**
- Eric W. Weisstein's World of Mathematics, Strehl identities

**Programs:** none

## A376462 — a(n) = Sum_{k = 0..n} binomial(n, k)^2*binomial(n+k, k)*A108625(n, n-k).

- OEIS: https://oeis.org/A376462
- offset: 0,2
- data: 1,5,109,3317,121501,4954505,216867925,9981053045,476860000285,23451310381505,1180189308268609,60519806861966105,31522855

**Formulas:**
- a(n) ~ (2/3 + sqrt(31) * cos(arccos(1597/(434*sqrt(31)))/3)/6) * (19 + 28*sqrt(7/3) * cos(arccos(3*sqrt(3/7)/2)/3))^n / (Pi*n)^2. - _Vaclav Kotesovec_, Oct 16 2025
- a(n) ~ (17 + 349/(4*(13*cos(Pi/7) - 8))) * 2^(7*n) * cos(Pi/7)^(7*n) / (26 * Pi^2 * n^2). - _Vaclav Kotesovec_, May 08 2026

**Comments (conjectures and context):**
- The sequence of Apéry numbers A005258 defined by A005258(n) = Sum_{k = 0..n} binomial(n, k)^2*binomial(n+k, k) satisfies the pair of supercongruences
- We conjecture that the present sequence satisfies the same pair of supercongruences. Some examples are given below.

**Links:**

**Programs:** none

## A333565 — O.g.f.: (1 + 4*x)/((1 + x)*sqrt(1 - 8*x)).

- OEIS: https://oeis.org/A333565
- offset: 0,2
- data: 1,7,33,223,1537,11007,80385,595455,4456449,33615871,255148033,1946337279,14908784641,114597822463,883479412737,682849298

**Formulas:**
- a(n) = (2^n)*binomial(2*n,n) + 3*sum_{k = 0..n-1} (-1)^(n+k+1)*2^k* binomial(2*k,k).
- a(n) = 4*A333564(n) + (-1)^n for n >= 1.
- a(n) = 2*A119259(n) - (-1)^n.
- a(n) = (-1)^n + 4*Sum_{k = 1..n} (3*k-1)*2^(k-1)*A000108(k-1).
- a(n) ~ 8^n * 4/(3*sqrt(Pi*n)).
- Congruences: a(p) == 7 ( mod p^3 ) for all prime p >= 3.
- O.g.f. A(x) = 1 + 7*x + 33*x^2 + ... satisfies the differential equation (x + 1)*(4*x + 1)*(8*x - 1)*A'(x) + (16*x^2 - 4*x + 7)*A(x) = 0. Cf. A333564.
- P-recursive: n*(3*n - 4)*a(n) = (21*n^2 - 40*n + 12)*a(n-1) + 4*(3*n - 1)*(2*n - 3)*a(n-2) with a(0) = 1 and a(1) = 7.

**Comments (conjectures and context):**
- This sequence satisfies the Gauss congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^k ), for all prime p and positive integers n and k, since the power series E(x) := exp( Sum_{n >= 1} a(n)*x^n/n ) has integer coefficients. See Stanley, Ex. 5.2 (a), p. 72, and its solution on p. 104.
- We conjecture that this sequence satisfies the stronger congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 3 and positive integers n and k. The particular case when n = k = 1 follows from the corresponding result for A333564. Some examples of these congruences are given below.

**Links:**

**Programs:** none

# F4

## A361711 — a(1) = 1 and a(n) = Sum_{k = 0..n-2} (-1)^k * binomial(n,k)^2 * binomial(n-2,k) for n >= 2.

- OEIS: https://oeis.org/A361711
- offset: 1,3
- data: 1,1,-8,5,126,-168,-2400,4125,50050,-98098,-1100736,2339064,25069968,-56279520,-585307008,1367240589,13919870250,-3351079

**Formulas:**
- a(2*n) = (-1)^n * (1/6) * (2*n-3)/(2*n-1) * (3*n)!/n!^3 = (-1)^n * (1/6) * (2*n-3)/(2*n-1) * A006480(n) for n >= 1.
- a(2*n+1) = (-1)^n * (3*n+1)/(2*n+1) * (3*n)!/n!^3 for n >= 1.
- a(2*n+1) = A361710(2*n+1) = A361716(2*n+1).
- a(n) = hypergeom([1 -n, -1 - n, -1 - n], [1, 1], 1).
- P-recursive: n^2*(n-2)*(3*n^2-14*n+17)*a(n) = -6*(6*n^3-24*n^2+29*n-9)*a(n-1) - 3*(n-3)*(3*n-4)*(3*n-5)*(3*n^2-8*n+6)*a(n-2) with a(1) = a(2) = 1.

**Comments (conjectures and context):**
- Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.

**Links:**
- Wikipedia, Dixon's identity.

**Programs:** (PARI) a(n) = if (n==1, 1, sum(k = 0, n-2, (-1)^k * binomial(n,k)^2 * binomial(n

## A364175 — a(n) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!).

- OEIS: https://oeis.org/A364175
- offset: 0,2
- data: 1,36,3564,408408,49697388,6249195036,802241960520,104466877291260,13746018177013356,1823169705017624880,2433310376616934

**Formulas:**
- a(n) ~ c^n * 1/sqrt(5*Pi*n) where c = (1296/25)*20^(1/3) = 140.7154092442799....
- a(n) = 93312*(2*n - 3)*(6*n - 1)*(6*n - 5)*(6*n - 7)*(6*n - 11)*(6*n - 13)*(6*n - 17)/(5*n*(n - 1)*(n - 2)*(5*n - 3)*(5*n - 6)*(5*n - 9)*(5*n - 12))*a(n-3) with a(0) = 1, a(1) = 36 and a(2) = 3564.
- a(n) = 3^n * (6*n)!/((3*n)!*(2*n)!) * 1/P where P = Product_{k = 1..n}  (2*n + 3*k). - _Peter Bala_, Jun 14 2026

**Comments (conjectures and context):**
- This sequence is only conjecturally an integer sequence.
- Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
- The integrality conjecture is true. See Links. - _David Radcliffe_, Jul 19 2026

**Links:**
- J. W. Bober, Factorial ratios, hypergeometric series, and a family of step functions, arXiv:0709.1977 [math.NT], 2007; J. London Math. Soc., 79, Issue 2, (2009), 422-444.
- David Radcliffe, Integrality of a Ratio of Fractional Factorials

**Programs:** none

## A364178 — a(n) = (10*n)!*(3*n)!*(n/2)!/((6*n)!*(5*n)!*(3*n/2)!*n!).

- OEIS: https://oeis.org/A364178
- offset: 0,2
- data: 1,168,83980,48664320,29966636700,19075222663168,12398706131799988,8175717823943147520,5447952226877283703580,36594423004

**Formulas:**
- a(n) ~ c^n * 1/sqrt(6*Pi*n), where c = (10/3)^5 * sqrt(3).
- a(n) = 1600*(10*n - 1)*(10*n - 3)*(10*n - 7)*(10*n - 9)*(10*n - 11)*(10*n - 13)*(10*n - 17)*(10*n - 19)/(27*n*(n - 1)*(3*n - 2)*(3*n - 4)*(6*n - 1)*(6*n - 5)*(6*n - 7)*(6*n - 11))*a(n-2) with a(0) = 1 and a(1) = 168.

**Comments (conjectures and context):**
- This sequence is only conjecturally an integer sequence.
- Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.

**Links:**
- J. W. Bober, Factorial ratios, hypergeometric series, and a family of step functions, arXiv:0709.1977 [math.NT], 2007; J. London Math. Soc., 79, Issue 2, (2009), 422-444.

**Programs:** none

# F5

## A370092 — a(0) = 1, a(n) = (-1)^n + (1/2) * Sum_{j=1..n} (1-(-1)^j-(-2)^j) * binomial(n,j) * a(n-j) for n > 0.

- OEIS: https://oeis.org/A370092
- offset: 0,3
- data: 1,1,3,16,105,856,8433,96916,1272225,18789136,308335713,5565837916,109603592145,2338198823416,53718370204593,132229213020

**Formulas:**
- E.g.f.: 2*exp(x)/(1 + exp(x) + exp(2*x) - exp(3*x)).

**Comments (conjectures and context):**
- Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k). For example, modulo 10 we obtain the sequence [1, 1, 3, 6, 5, 6, 3, 6, 5, 6, 3, 6, 5, 6, 3, 6, 5, 6, ...] with an apparent period of 4 beginning at a(2). See A000670 for a more general conjecture. - _Peter Bala_, Feb 16 2024

**Links:**
- Andrew Howroyd, Table of n, a(n) for n = 0..200

**Programs:** (SageMath) | def a(m):

# done/context (already proved by others — reference only)

## A333096 — a(n) = the n-th order Taylor polynomial (centered at 0) of c(x)^(4*n) evaluated at x = 1, where c(x) = (1 - sqrt(1 - 4*x))/(2*x) is the o.g.f. of the sequence of Catalan numbers A000108.

- OEIS: https://oeis.org/A333096
- offset: 0,2
- data: 1,5,53,647,8373,111880,1525511,21093476,294663349,4148593604,58770091928,836722722951,11961868391175,171601856667701,246

**Formulas:**
- a(n) = Sum_{k = 0..n} 4*n/(4*n+k)*binomial(4*n+2*k-1, k) for n >= 1.
- a(n) = [x^n] ( (1 + x)*c^4(x/(1 + x)) )^n.
- O.g.f.: ( 1 + x*f'(x)/f(x) )/( 1 - x*f(x) ), where f(x) = 1 + 4*x + 30*x^2 + 280*x^3 + 2925*x^4 + ... = (1/x)*Revert( x/c^4(x) ) is the o.g.f. of A212073.
- Row sums of the Riordan array ( 1 + x*f'(x)/f(x), f(x) ) belonging to the Hitting time subgroup of the Riordan group.
- a(n) ~ 2^(6*n + 3) * 3^(6*n + 3/2) / (31 * sqrt(Pi*n) * 5^(5*n + 1/2)). - _Vaclav Kotesovec_, Mar 28 2020
- a(n) = Sum_{k = 0..n} 4*n/(4*n+2*k)*binomial(4*n+2*k, k) for n >= 1. - _Peter Bala_, May 03 2024
- From _Seiichi Manyama_, Jun 29 2026: (Start)
- G.f.: g^2 * (2-g)/((6-5*g) * (1-g+g^2)) where g = 1+x*g^6 is the g.f. of A002295.

**Comments (conjectures and context):**
- The sequence satisfies the Gauss congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^k ) for all prime p and positive integers n and k.
- We conjecture that the sequence satisfies the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Examples of these congruences are given below.
- More generally, for each integer m, we conjecture that the sequence a_m(n) := the n-th order Taylor polynomial of c(x)^(m*n) evaluated at x = 1 satisfies the same supercongruences. For cases see A099837 (m = -2), A100219 (m = -1), A000012 (m = 0), A333093 (m = 1), A333094 (m = 2), A333095 (m = 3), A333097 (m = 5).
- Adamczewski includes proof abstract regarding the above conjecture in linked article. - _Michael De Vlieger_, Aug 18 2026

**Links:**
- Michael De Vlieger, Table of n, a(n) for n = 0..853
- Tom Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?, arXiv:2608.11941 [cs.AI], 2026. See p. 9 (proof, Appendix A).

**Programs:** none

## A333095 — a(n) = the n-th order Taylor polynomial (centered at 0) of c(x)^(3*n) evaluated at x = 1, where c(x) = (1 - sqrt(1 - 4*x))/(2*x) is the o.g.f. of the sequence of Catalan numbers A000108.

- OEIS: https://oeis.org/A333095
- offset: 0,2
- data: 1,4,34,337,3554,38754,431521,4874377,55639010,640177033,7412165034,86256322816,1007980394849,11820510331777,139032549536

**Formulas:**
- a(n) = Sum_{k = 0..n} 3*n/(3*n+k)*binomial(3*n+2*k-1, k) for n >= 1.
- a(n) = [x^n] ( (1 + x)*c^3(x/(1 + x)) )^n.
- O.g.f.: ( 1 + x*f'(x)/f(x) )/( 1 - x*f(x) ), where f(x) = 1 + 3*x + 18*x^2 + 136*x^3 + 1155*x^4 + ... = (1/x)*Revert( x/c^3(x) ) is the o.g.f. of A118970.
- Row sums of the Riordan array ( 1 + x*f'(x)/f(x), f(x) ) belonging to the Hitting time subgroup of the Riordan group.
- a(n) ~ 5^(5*n + 3/2) / (7 * 2^(8*n + 3/2) * sqrt(Pi*n)). - _Vaclav Kotesovec_, Mar 28 2020
- a(n) = Sum_{k = 0..n} 3*n/(3*n+2*k)*binomial(3*n+2*k, k) for n >= 1. - _Peter Bala_, May 03 2024
- From _Seiichi Manyama_, Jun 29 2026: (Start)
- G.f.: g^2 * (2-g)/((5-4*g) * (1-g+g^2)) where g = 1+x*g^5 is the g.f. of A002294.

**Comments (conjectures and context):**
- The sequence satisfies the Gauss congruences: a(n*p^k) == a(n*p^(k-1)) ( mod p^k ) for all prime p and positive integers n and k.
- We conjecture that the sequence satisfies the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k. Examples of these congruences are given below.
- More generally, for each integer m, we conjecture that the sequence a_m(n) := the n-th order Taylor polynomial of c(x)^(m*n) evaluated at x = 1 satisfies the same supercongruences. For cases see A099837 (m = -2), A100219 (m = -1), A000012 (m = 0), A333093 (m = 1), A333094 (m = 2), A333096 (m = 4), A333097 (m = 5).

**Links:**

**Programs:** none

## A003161 — A binomial coefficient sum.

- OEIS: https://oeis.org/A003161
- offset: 0,3
- data: 1,1,2,9,36,190,980,5705,33040,204876,1268568,8209278,53105976,354331692,2364239592,16140234825,110206067400,765868074400

**Formulas:**
- a(n) = Sum_{k=0..n} A120730(n,k)^3. - _Philippe Deléham_, Oct 18 2008
- G.f.: hypergeometric expression with an anti-derivative, see Maple program. - _Mark van Hoeij_, May 06 2013
- Recurrence: n*(n+1)^3*(7*n^2 - 14*n + 3)*a(n) = - n*(7*n^5 - 112*n^4 + 206*n^3 + 8*n^2 - 125*n + 48)*a(n-1) + 16*(n-1)*(28*n^5 - 133*n^4 + 194*n^3 - 33*n^2 - 120*n + 61)*a(n-2) + 64*(n-2)^3*(n-1)*(7*n^2 - 4)*a(n-3). - _Vaclav Kotesovec_, Mar 06 2014
- a(n) ~ 2^(3*n+9/2) / (9 * Pi^(3/2) * n^(5/2)). - _Vaclav Kotesovec_, Mar 06 2014
- a(n) = Sum_{j=0..floor(n/2)} A008315(n,j)^3. - _Alois P. Heinz_, Oct 17 2022

**Comments (conjectures and context):**
- Conjecture: Let b(n) = a(2*n-1). Then the supercongruence b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k)) holds for positive integers n and k and all primes p >= 5. (End)

**Links:**
- Alois P. Heinz, Table of n, a(n) for n = 0..1116
- F. Bergeron, L. Favreau and D. Krob, Conjectures on the enumeration of tableaux of bounded height, Discrete Math, vol. 139, no. 1-3 (1995), 463-468.
- H. W. Gould, Problem E2384, Amer. Math. Monthly, 81 (1974), 170-171.

**Programs:** (PARI) a(n)=sum(k=0,n\2, (binomial(n,k)-binomial(n,k-1))^3) /* _Michael Somos_, 

## A277060 — a(n) = (1/2) * Sum_{k=0..n} (binomial(n,k) * binomial(n+k,k+1))^2 for n >= 0.

- OEIS: https://oeis.org/A277060
- offset: 0,3
- data: 0,1,28,729,19376,529575,14835780,424231465,12338211520,363931754949,10862528888300,327501958094003,9959845931792784,3051

**Formulas:**
- a(n) = n^2 * A074635(n)/2.
- From _Peter Bala_, Mar 22 2023: (Start)
- a(n) = Sum_{k = 0..n-1} binomial(n+1,k)*binomial(n-1,k)*binomial(n+k,k)^2.
- P-recursive: (n-1)^2*(3*n^2-6*n+2)*(n+1)^3*a(n) = (2*n-1)*(51*n^4-102*n^3+19*n^2+ 32*n-14)*n^2*a(n-1) - n^2*(n-2)*(3*n^2-1)*(n-1)^2*a(n-2) with a(0) = 0 and a(1) = 1.
- a(n) ~ sqrt(12 + 17*sqrt(2)/2)*(17 + 12*sqrt(2))^n/(4*n^(3/2)*Pi^(3/2)). (End)

**Comments (conjectures and context):**
- Conjecture: the supercongruences a(p-1) == 1 (mod p^4) holds for all primes p >= 5 and a(p^2-1) == 1 (mod p^5) holds for all primes p >= 3. - _Peter Bala_, Mar 22 2023
- The conjecture is true (see Epstein link). - _Andrew R. Epstein_, Sep 21 2026

**Links:**
- Seiichi Manyama, Table of n, a(n) for n = 0..656
- Andrew R. Epstein, Proof of a conjecture in A277060, 2026.

**Programs:** (PARI) a(n)=my(t=n); if(n<2, return(n)); sum(k=1,n, t*=(n-k+1)*(n+k)/k/(k+1); t^
