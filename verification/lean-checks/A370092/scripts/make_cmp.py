"""Comparator layout for A370092 (cmp-ws, Lean v4.27.0), generated from the fc-ws proof files.
A370092Defs: the official challenge file cut before the theorem's docstring (definitions verbatim by construction).
Proof modules: imports BalaCheck.X -> Submission.X, target -> Submission.A370092Defs.
A370092Full: the final theorem with an explicit statement; Spec: the official name; NegWeak: P ∣ 2 * totient k (true, weaker; must be rejected)."""
import pathlib, re
import os
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; SUB = L / "cmp-ws/Submission"
ch = (pathlib.Path(os.environ["LOP_ISOLATED"]) / "oeis_370092_conjecture_0.lean").read_text()
cut = ch.index("/--\n%C A370092 Conjecture")
(SUB / "A370092Defs.lean").write_text(ch[:cut].rstrip() + "\n")
def ren(s):
    s = s.replace("import FormalConjectures.OEIS.Auto.«370092_862cfcda»", "import Submission.A370092Defs")
    return re.sub(r"^import BalaCheck\.", "import Submission.", s, flags=re.M)
for m in ["A370092Formula", "A370092Odd", "A370092Two"]:
    (SUB / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text())); print("copied", m)
main = ren((FC / "A370092Main.lean").read_text())
old = "theorem A370092_from_target : type_of% @oeis_370092_conjecture_0 := by"
assert main.count(old) == 1
STMT = "∀ (k : ℕ), 2 < k → ∃ P : ℕ, P ∣ Nat.totient k ∧ eventually_periodic (a_mod_k k) P"
(SUB / "A370092Full.lean").write_text(main.replace(old, f"theorem A370092_full : {STMT} := by")); print("A370092Full")
SIG = "(k : ℕ) (hk : 2 < k) :\n    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P"
assert " ".join(SIG.split()) in " ".join(ch.split()), "statement text differs from the challenge"
(SUB / "A370092Spec.lean").write_text(f"import Submission.A370092Full\n\nopen Finset Nat\n\ntheorem oeis_370092_conjecture_0 {SIG} :=\n  A370092_full k hk\n")
(SUB / "A370092NegWeak.lean").write_text(f"import Submission.A370092Full\n\nopen Finset Nat\n\n-- control: weaker statement (period divides 2·φ(k)), must be rejected by Comparator\ntheorem oeis_370092_conjecture_0 {SIG.replace('P ∣ totient k', 'P ∣ 2 * totient k')} := by\n  obtain ⟨P, hP, hper⟩ := A370092_full k hk\n  exact ⟨P, dvd_mul_of_dvd_right hP 2, hper⟩\n")
print("Spec, NegWeak")
