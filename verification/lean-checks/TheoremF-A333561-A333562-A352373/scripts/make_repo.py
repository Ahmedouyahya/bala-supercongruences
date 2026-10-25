"""Repository (Lean v4.35.0) version of the Theorem F proof and its OEIS instances A333561, A333562, A352373,
generated from the fc-ws (v4.27.0) files in fc-ws/BalaCheck (which are not modified).
EpochA333042.lean: the source header and the FormalConjectures import are replaced by a source/permission header
  and `import Mathlib`; everything from `namespace Epoch333042` to the end is copied verbatim.
TFSetup .. TFInst: imports renamed (BalaCheck.X -> BalaProofs.X; BalaCheck.EpochExp -> BalaProofs.EpochA333042),
  otherwise verbatim.
A333562Ident: the target import is replaced by `import BalaProofs.A333562Defs`, otherwise verbatim.
<E>Defs.lean: import Mathlib + the target's open line + the target's definition block (with docstring) verbatim
  (the target's sample theorems a_zero, a_one, ... are left out; several are `sorry` there).
<E>Main.lean: the instance file (imports renamed; target import -> Mathlib + BalaProofs.<E>Defs) without its final
  type_of% theorem.
<E>.lean: the target's open line, theorem docstring and statement verbatim (up to `:=`), then the proof body of
  <E>_from_target; for A333562 the first intro line drops `p n k` (they are binders of the target statement).
Later manual edits for Lean v4.35 / current Mathlib are logged in PORT-LOG.md."""
import pathlib, re
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; W = pathlib.Path(os.environ["BALA_WORK_LEAN"])
T = REPO / "statements/lean-targets"

def write(name, text):
    p = W / f"{name}.lean"
    assert not p.exists() or name in NEW, p
    p.write_text(text); print("wrote", p.name)

ENTRIES = {  # entry: (target file, open line, def-block start, def-block end, theorem start, proof-end marker, old/new intro)
    "A333561": ("333561_b286c526", "open Nat Finset", "/--\nA333561: $a(n)", "theorem a_zero",
                "/-- We conjecture that this sequence satisfies the supercongruences", ":=\nby sorry", None),
    "A333562": ("333562_2eccaf4c", "open Nat Finset", "/--\nA333562: $a(n)", "theorem a_zero",
                "/--\nWe conjecture that this sequence satisfies the congruences", ":= by\n  sorry",
                ("  intro p n k hp hp5 hn hk\n", "  intro hp hp5 hn hk\n")),
    "A352373": ("352373_a1d5fa75", "open scoped BigOperators Nat Finset Int", "/--\nA352373: $a(n)", "lemma a_one",
                "/--\nA352373 Conjecture:", ":=\nby sorry", None),
}
TF = ["TFSetup", "TFFrob", "TFHarmonic", "TFEps", "TFLift", "TFMain", "TFInst"]
NEW = {"EpochA333042", *TF, "A333562Ident"} | {f"{e}{s}" for e in ENTRIES for s in ("Defs", "Main", "")}

def ren(s):
    for e, (tf, *_rest) in ENTRIES.items():
        s = s.replace(f"import FormalConjectures.OEIS.Auto.«{tf}»", f"import Mathlib\nimport BalaProofs.{e}Defs")
    s = s.replace("import BalaCheck.EpochExp\n", "import BalaProofs.EpochA333042\n")
    return re.sub(r"^import BalaCheck\.", "import BalaProofs.", s, flags=re.M)

# 1. Epoch AI's A333042 proof
src = (FC / "EpochExp.lean").read_text()
k = src.index("namespace Epoch333042\n")
assert src[:k].count("\n") == 4 and src.startswith("import FormalConjectures.Util.ProblemImports\n")
HEADER = """/-
Source: Epoch AI, OEIS Open evaluation, run oeis-lite-200usd-fable-i7s7n9q7v4emgjp7, item
general_supercongruence_conjecture (A333042), accepted (SafeVerify). Used with the permission of Epoch AI.
Changes from the original: the import line (Mathlib instead of FormalConjectures.Util.ProblemImports)
and the enclosing namespace Epoch333042. Any further change (for Lean v4.35.0 and current Mathlib) is listed below this line.
-/
import Mathlib

"""
write("EpochA333042", HEADER + src[k:])

# 2. Theorem F modules
for m in TF:
    write(m, ren((FC / f"{m}.lean").read_text()))

# 3. A333562 identity
s = (FC / "A333562Ident.lean").read_text()
old = "import FormalConjectures.OEIS.Auto.«333562_2eccaf4c»\n"
assert s.count(old) == 1
write("A333562Ident", s.replace(old, "import BalaProofs.A333562Defs\n"))

# 4. per entry: Defs, Main, final theorem
for e, (tf, opn, d0, d1, t0, t1, intro) in ENTRIES.items():
    t = (T / f"{tf}.lean").read_text()
    assert t.count(opn + "\n") == 1 and t.count(d0) == 1 and t.count(t0) == 1
    i = t.index(d0); j = t.index(d1); l = t.index(t0); m = t.index(t1, l)
    defs = t[i:j].rstrip() + "\n"
    assert "theorem" not in defs and "lemma" not in defs and "sorry" not in defs
    write(f"{e}Defs", "import Mathlib\n\n" + opn + "\n\n" + defs)
    main = ren((FC / f"{e}.lean").read_text())
    hits = re.findall(rf"^theorem {e}_from_target : type_of% @\S+ := by\n", main, flags=re.M)
    assert len(hits) == 1
    head, body = main.split(hits[0])
    write(f"{e}Main", head.rstrip() + "\n")
    if intro:
        assert body.startswith(intro[0]); body = intro[1] + body[len(intro[0]):]
    write(e, f"import BalaProofs.{e}Main\n\n{opn}\n\n" + t[l:m] + ":= by\n" + body)
