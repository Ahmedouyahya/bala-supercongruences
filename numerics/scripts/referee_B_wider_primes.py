#!/usr/bin/env python3
"""
Re-run the independent referee-B assembly check of notes/A376462-shifted-congruence-proof.md
at larger primes: (p,r,m) = (11,2,1), (13,2,1), (7,2,2).
r = 3 at a second prime and r = 4 exercise two and three genuine induction steps of section 4/5.
Output: numerics/out/referee_B_wider_primes.txt
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import referee_B_shifted_assembly as rb

cases = [(11, 2, 1), (13, 2, 1), (7, 2, 2)]
for case in cases:
    t0 = time.time()
    rb.run(*case)
    rb.out(f"[timing] case {case}: {time.time()-t0:.1f} s")
    rb.out("")
rb.out("=" * 78)
if rb.FAILS:
    rb.out(f"FAILURES ({len(rb.FAILS)}):")
    for f_ in rb.FAILS:
        rb.out("  - " + f_)
else:
    rb.out("No structural failures at the deeper cases.")
nfail = sum(1 for l in rb.LINES if "FAIL" in l and "FAILURES" not in l)
nok = sum(1 for l in rb.LINES if l.lstrip().startswith("ok") or " ok " in l or l.lstrip().startswith("OK"))
rb.out(f"lines containing FAIL: {nfail}")
here = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(here, "out", "referee_B_wider_primes.txt"), "w") as fh:
    fh.write("\n".join(rb.LINES) + "\n")
