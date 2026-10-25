import BalaProofs.A333565Bridge
import BalaProofs.TFMain
import BalaProofs.TFInst
import BalaProofs.TF3Main

/-!
# A333565 from Theorem F (p ≥ 5) and Theorem F₃(ii) (p = 3)

`A333565 n = 2 B(n) - (-1)^n` (`A333565.A333565_eq`), and `B(N) = [x^N] ((1+x)^2 (1-x)^{-1})^N`
for `N ≥ 1` (`A333565.B_eq_coeffForm`, `TF.A_m_neg_one 2 1`), i.e. `(a, b, c) = (2, -1, 1)`.
For `p ≥ 5` use `TF.tower_int`, for `p = 3` use `TF.tower_three`; since `p` is odd, `n p^k` and
`n p^{k-1}` have the same parity, so `A333565(n p^k) - A333565(n p^{k-1}) = 2 (B(n p^k) - B(n p^{k-1}))`.
-/
