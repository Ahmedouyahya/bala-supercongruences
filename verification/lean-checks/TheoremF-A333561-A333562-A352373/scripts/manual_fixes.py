"""The manual v4.35 edits (each logged in PORT-LOG.md) to BalaProofs/EpochA333042.lean and BalaProofs/TFLift.lean,
as one replayable script. Run after make_repo.py. Every replacement asserts the exact number of occurrences."""
import pathlib
import os
p = pathlib.Path(os.environ["BALA_WORK_LEAN"]) / "EpochA333042.lean"
s = p.read_text()
def rep(old, new, n):
    global s
    assert s.count(old) == n, (old, s.count(old)); s = s.replace(old, new)
for o in ["copyright.formalConjectures", "moduleDocstring", "namespace"]:
    rep(f"set_option linter.style.{o} false\n", "", 1)
rep("d⁄dX ℚ", "d⁄dX", 30)
rep("padicValNat.pow _ (Nat.factorial_ne_zero k)", "padicValNat.pow k.factorial m", 1)
rep("rw [Finset.mem_antidiagonal] at hx", "rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx", 2)
rep("∑ x ∈ Finset.antidiagonal (n*t),", "∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n*t),", 2)
rep("∀ x ∈ Finset.antidiagonal k, coeff x.1 c1S", "∀ x ∈ Finset.HasAntidiagonal.antidiagonal k, coeff x.1 c1S", 1)
rep("        rw [gec_succ]\n        simp only at hS ⊢\n", "        rw [gec_succ]\n        try simp only at hS ⊢\n", 1)
rep("    have := congrArg (fun φ => coeff k φ) hD\n    simp only at this\n", "    have := congrArg (fun φ => coeff k φ) hD\n    try simp only at this\n", 1)
rep("  have h := congrArg (fun φ => coeff k φ) (deriv_pow F ℓ)\n  simp only at h\n", "  have h := congrArg (fun φ => coeff k φ) (deriv_pow F ℓ)\n  try simp only at h\n", 1)
HEAD = "Any further change (for Lean v4.35.0 and current Mathlib) is listed below this line.\n-/\n"
LIST = """  - removed `set_option linter.style.copyright.formalConjectures false`, `set_option linter.style.moduleDocstring false`
    and `set_option linter.style.namespace false`: these options are registered by Formal Conjectures' own linters
    (FormalConjectures/Util/Linters), which `import Mathlib` does not load; Lean v4.35 rejects unknown options (3 lines)
  - `d⁄dX ℚ` -> `d⁄dX`: `PowerSeries.derivative` now takes the coefficient ring implicitly, so the notation `d⁄dX`
    no longer takes the ring as an argument (30 places)
  - `padicValNat.pow _ (Nat.factorial_ne_zero k)` -> `padicValNat.pow k.factorial m` in vc_add_eq: the lemma now
    takes `(a n : ℕ)` and no longer needs `a ≠ 0` (1 place)
  - `Finset.mem_antidiagonal` -> `Finset.HasAntidiagonal.mem_antidiagonal` in coeff_pow_congr and coeff_trunc_pow_key
    (2 places), `Finset.antidiagonal` -> `Finset.HasAntidiagonal.antidiagonal` in coeff_mul_expand (2 places) and d_c1S
    (1 place): Mathlib renamed `Finset.addAntidiagonal` to `Finset.antidiagonal`, which now takes precedence over the
    `HasAntidiagonal` names exported to `Finset`
  - `simp only at this` / `simp only at h` / `simp only at hS ⊢` -> `try simp only at ...` in isExpOf_iff_deriv,
    coeff_succ_pow_succ and gec_eq_coeff: under Lean v4.35 these lemma-free `simp only` calls make no progress
    (an error); the following steps are unchanged (3 places)
-/
"""
rep(HEAD, HEAD[:-3] + LIST, 1)
p.write_text(s); print("applied")

q = p.with_name("TFLift.lean"); t = q.read_text()
old = "  intro x hx\n  rw [mem_antidiagonal] at hx\n"; assert t.count(old) == 1
q.write_text(t.replace(old, "  intro x hx\n  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx\n")); print("applied TFLift")
