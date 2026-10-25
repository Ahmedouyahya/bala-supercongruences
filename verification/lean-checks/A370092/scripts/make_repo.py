"""Repository (Lean v4.35.0) version of the A370092 proof, generated from the fc-ws (v4.27.0) files.
A370092Defs.lean: import Mathlib + the target's open line + the target's three definitions (with docstrings) verbatim
(the target's sample theorems a_zero..a_three are `sorry` there and are left out). Proof modules: imports renamed.
A370092.lean: the target's docstring and theorem statement verbatim, proof body unchanged."""
import pathlib, re
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; W = pathlib.Path(os.environ["BALA_WORK_LEAN"])
t = (REPO / "statements/lean-targets/370092_862cfcda.lean").read_text()
i = t.index("/--\nA370092: $a(0) = 1$"); j = t.index("theorem a_zero")
k = t.index("/-- A sequence `f` is eventually periodic"); l = t.index("/--\n%C A370092 Conjecture")
m = t.index(":= by\n  sorry", l)
defs = t[i:j].rstrip() + "\n\n" + t[k:l].rstrip() + "\n"
assert "theorem" not in defs and "sorry" not in defs
(W / "A370092Defs.lean").write_text("import Mathlib\n\nopen Finset Nat\n\n" + defs)
def ren(s):
    s = s.replace("import FormalConjectures.OEIS.Auto.«370092_862cfcda»", "import Mathlib\nimport BalaProofs.A370092Defs")
    return re.sub(r"^import BalaCheck\.", "import BalaProofs.", s, flags=re.M)
for f in ["A370092Formula", "A370092Odd", "A370092Two"]:
    (W / f"{f}.lean").write_text(ren((FC / f"{f}.lean").read_text())); print("wrote", f)
main = ren((FC / "A370092Main.lean").read_text())
old = "theorem A370092_from_target : type_of% @oeis_370092_conjecture_0 := by\n  intro k hk\n"
assert main.count(old) == 1
head, body = main.split(old)
(W / "A370092Main.lean").write_text(head.rstrip() + "\n")
(W / "A370092.lean").write_text("import BalaProofs.A370092Main\n\nopen Finset Nat\n\n" + t[l:m] + ":= by\n" + body)
print("wrote A370092Main, A370092.lean")
