"""Comparator layout for A363983 (cmp-ws, Lean v4.27.0). Every file is generated from the fc-ws proof files:
imports BalaCheck.X -> Submission.X; the target import -> Submission.A363983Defs (the target's definition block copied verbatim);
the final theorem `A363983_from_target : type_of% @...` -> `A363983_full : <statement>` with the same proof; Spec states the
official theorem; NegWeak states it with modulus p^(3r-1) (must be rejected)."""
import pathlib, re
import os
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; SUB = L / "cmp-ws/Submission"
tgt = (L / "fc-ws/FormalConjectures/OEIS/Auto/363983_3f7e4c53.lean").read_text()
i = tgt.index("/--\nA363983: The sequence"); j = tgt.index("/-- oeis_363983_conjecture_0")
defblock = tgt[i:j].rstrip() + "\n"
assert defblock.count("def A363983 ") == 1
(SUB / "A363983Defs.lean").write_text("import FormalConjectures.Util.ProblemImports\n\nopen Nat Finset Int\n\n" + defblock)
def ren(s):
    s = s.replace("import FormalConjectures.OEIS.Auto.«363983_3f7e4c53»", "import Submission.A363983Defs")
    return re.sub(r"^import BalaCheck\.", "import Submission.", s, flags=re.M)
for m in ["OSSLib", "A363983Rec", "A363983Lemmas"]:
    (SUB / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text())); print("copied", m)
STMT = ("∀ (p n r : ℕ), Nat.Prime p → p ≥ 5 → n > 0 → r > 0 →\n"
        "    (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)]")
main = ren((FC / "A363983Main.lean").read_text())
old = "theorem A363983_from_target : type_of% @oeis_A363983_conjecture_supercongruence := by"
assert main.count(old) == 1
(SUB / "A363983Full.lean").write_text(main.replace(old, f"theorem A363983_full :\n    {STMT} := by")); print("A363983Full")
SIG = ("(p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :\n"
       "  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)]")
assert SIG.replace("\n", " ").replace("  ", " ") in tgt.replace("\n", " ").replace("  ", " ")
(SUB / "A363983Spec.lean").write_text(f"import Submission.A363983Full\n\nopen Nat Finset Int\n\ntheorem oeis_A363983_conjecture_supercongruence {SIG} :=\n  A363983_full p n r hp h_p_ge_5 hn hr\n")
(SUB / "A363983NegWeak.lean").write_text(f"import Submission.A363983Full\n\nopen Nat Finset Int\n\n-- control: weaker modulus, must be rejected by Comparator\ntheorem oeis_A363983_conjecture_supercongruence {SIG.replace('(3 * r)', '(3 * r - 1)')} :=\n  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A363983_full p n r hp h_p_ge_5 hn hr)\n")
print("Spec, NegWeak written")
