"""Repository (Lean v4.35.0) version of the A363983 proof, generated from the fc-ws (v4.27.0) files.
A363983Defs.lean: import Mathlib + the target's open line + the target's definition block verbatim.
OSSLib, A363983Rec, A363983Lemmas, A363983Main: imports renamed (BalaCheck.X -> BalaProofs.X, target -> BalaProofs.A363983Defs);
Main without the final type_of% theorem. A363983.lean: the target's docstring and theorem statement verbatim, proof body unchanged.
Later manual edits for Mathlib renames are logged in PORT-LOG.md."""
import pathlib, re
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; W = pathlib.Path(os.environ["BALA_WORK_LEAN"])
tgt = (REPO / "statements/lean-targets/363983_3f7e4c53.lean").read_text()
i = tgt.index("/--\nA363983: The sequence"); j = tgt.index("/-- oeis_363983_conjecture_0"); k = tgt.index(":= by\n  sorry", j)
defblock = tgt[i:j].rstrip() + "\n"; thmblock = tgt[j:k]          # docstring + statement, up to ':='
(W / "A363983Defs.lean").write_text("import Mathlib\n\nopen Nat Finset Int\n\n" + defblock)
def ren(s):
    s = s.replace("import FormalConjectures.OEIS.Auto.«363983_3f7e4c53»", "import Mathlib\nimport BalaProofs.A363983Defs")
    return re.sub(r"^import BalaCheck\.", "import BalaProofs.", s, flags=re.M)
for m in ["OSSLib", "A363983Rec", "A363983Lemmas"]:
    (W / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text())); print("wrote", m)
main = ren((FC / "A363983Main.lean").read_text())
old = "theorem A363983_from_target : type_of% @oeis_A363983_conjecture_supercongruence := by\n  intro p n r hp hp5 hn hr\n"
assert main.count(old) == 1
head, body = main.split(old)
(W / "A363983Main.lean").write_text(head.rstrip() + "\n")
body = body.replace("hp5", "h_p_ge_5")
(W / "A363983.lean").write_text("import BalaProofs.A363983Main\n\nopen Nat Finset Int\n\n" + thmblock + ":= by\n" + body)
print("wrote A363983Main (without the type_of% theorem) and A363983.lean")
