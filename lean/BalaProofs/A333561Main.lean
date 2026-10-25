import BalaProofs.TFMain
import BalaProofs.TFInst
import Mathlib
import BalaProofs.A333561Defs

/-!
# A333561 from Theorem F

The target's `a n = Σ_{k ≤ 2n} C(3n, 2n-k) C(n+k-1, k)` is `[x^{2n}] ((1+x)^3 (1-x)^{-1})^n`,
i.e. Theorem F with `(a, b, c) = (3, -1, 2)` (`TF.A_m_neg_one`, `TF.tower_int`).
-/
