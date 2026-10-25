import BalaProofs.TFMain
import BalaProofs.TFInst
import Mathlib
import BalaProofs.A352373Defs

/-!
# A352373 from Theorem F

The target's `a n = Σ_{k ≤ n/2} C(3n-2k-1, n-2k) C(n+k-1, k)` (n ≥ 1) is
`[x^n] ((1-x)^{-2} (1-x^2)^{-1})^n = [x^n] ((1+x)^{-1} (1-x)^{-3})^n`,
i.e. Theorem F with `(a, b, c) = (-1, -3, 1)` (`TF.A_neg_one_neg_three`, `TF.tower_int`).
-/
