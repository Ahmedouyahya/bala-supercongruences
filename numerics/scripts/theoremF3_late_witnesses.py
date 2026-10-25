# Paper A, remark after Theorem 1.2: smallest witness M (or None) for the triples left open by the search to M<=40.
# Usage: python3 theoremF3_late_witnesses.py Mmax
import sys
exec(open('numerics/scripts/theoremF3_exceptions_search.py').read().split('R=int(sys.argv[1])')[0])
L=[(-17,-17,7),(-15,11,7),(-9,-8,8),(-9,-5,8),(-8,15,8),(-4,14,5),(1,15,8),(-8,18,8),(-5,15,5),(-2,18,8)]
for t in L: print(t, first_M(*t,int(sys.argv[1])), flush=True)
