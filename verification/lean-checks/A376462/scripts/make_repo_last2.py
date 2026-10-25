"""Repository (Lean v4.35.0) versions of A376462 and A333565, generated from the fc-ws (v4.27.0) files.
<E>Defs.lean: import Mathlib + the target's open line + the target's definitions (with docstrings) verbatim (sample theorems
left out). Proof modules: imports BalaCheck.X -> BalaProofs.X, target -> BalaProofs.<E>Defs. <E>Main: the final file without
its type_of% theorem. <E>.lean: the target's docstring and statement verbatim, then the proof body."""
import pathlib, re
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
FC = pathlib.Path(os.environ["BALA_CHECK_DIR"]) / "fc-ws/BalaCheck"
W = pathlib.Path(os.environ["BALA_WORK_LEAN"]); T = REPO / "statements/lean-targets"
def defblocks(t):
    return re.findall(r"(/--(?:(?!-/).)*-/\s*\n(?:noncomputable )?def .*?)(?=\n\s*\n|\n(?:theorem|lemma|/--))", t, re.S)
def ren(s, tgt, E):
    s = s.replace(f"import FormalConjectures.OEIS.Auto.«{tgt}»", f"import Mathlib\nimport BalaProofs.{E}Defs")
    return re.sub(r"^import BalaCheck\.", "import BalaProofs.", s, flags=re.M)
for E, tgt, opens, mods, last, head, intro_old, intro_new in [
  ("A376462", "376462_96154f2f", "open Nat Finset",
   ["ShiftLibProd", "ShiftLibHarm", "ShiftLibBlock", "A376462Rep", "A376462Kernel", "A376462Classes", "A376462First",
    "A376462ShiftRep", "A376462ShiftK", "A376462ShiftJ", "A376462ShiftB", "A376462ShiftS", "A376462ShiftMain"],
   "A376462Main", "theorem oeis_376462_conjecture_0 :", None, None),
  ("A333565", "333565_757e3efd", "open Nat Int BigOperators",
   ["A333565Bridge", "TF3Harm", "TF3G", "TF3Exp", "TF3Main"],
   "A333565", "theorem oeis_A333565_conjecture_strong_gauss_congruence", "  intro p n k hp hp3 hn hk\n", "")]:
    t = (T / f"{tgt}.lean").read_text(); bl = defblocks(t); assert bl, E
    (W / f"{E}Defs.lean").write_text("import Mathlib\n\n" + opens + "\n\n" + "\n\n".join(b.strip() for b in bl) + "\n")
    for m in mods:
        (W / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text(), tgt, E))
    main = ren((FC / f"{last}.lean").read_text(), tgt, E)
    old = re.search(r"theorem \w+_from_target : type_of% @\w+ := by\n", main).group(0)
    hd, body = main.split(old)
    if intro_old: assert body.startswith(intro_old); body = intro_new + body[len(intro_old):]
    mainname = f"{E}Main" if last == E else last
    (W / f"{mainname}.lean").write_text(hd.rstrip() + "\n")
    ti = t.index(head); di = t.rfind("/--", 0, ti); stmt = t[di:t.index(":= by sorry", ti) if ":= by sorry" in t[ti:] else t.index(":=", ti)]
    (W / f"{E}.lean").write_text(f"import BalaProofs.{mainname}\n\n{opens}\n\n" + stmt.rstrip() + " := by\n" + body)
    print(E, "defs blocks", len(bl), "modules", len(mods), "main", mainname)
