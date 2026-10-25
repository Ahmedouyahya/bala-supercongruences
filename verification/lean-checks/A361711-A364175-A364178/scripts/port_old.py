"""Generate the benchmark-environment (Lean v4.27.0, fc-ws) versions of the repository proofs of A361711, A364175, A364178.
Helpers: copied verbatim except `import BalaProofs.X` -> `import BalaCheck.Old.X`.
Main files: the copied target definition (and our a_zero for A364175) is removed and the target module is imported instead;
our final theorem keeps its statement and proof under a primed name; a last theorem takes its type from the target via type_of%.
Every change is printed. Any later manual edit (Mathlib renames for v4.27) is logged in LOG.md."""
import re, pathlib, sys
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
SRC = REPO / "lean/BalaProofs"
DST = pathlib.Path(os.environ["BALA_CHECK_DIR"]) / "fc-ws/BalaCheck/Old"
HELPERS = ["UnitSquaresCore", "UnitSquares", "InvSquares", "UnitSums", "UnitProduct", "BlockProduct",
           "ProductSplit", "FactorialSplit", "FloorCounting", "GammaShift", "ClosedForm"]
def ren(s): return re.sub(r"^import BalaProofs\.", "import BalaCheck.Old.", s, flags=re.M)
for h in HELPERS:
    (DST / f"{h}.lean").write_text(ren((SRC / f"{h}.lean").read_text()))
    print("helper", h)
def cut(s, start_pat, end_pat):
    """remove from the line matching start_pat up to (not including) the line matching end_pat; return (new, removed)"""
    lines = s.split("\n"); i = next(k for k, l in enumerate(lines) if re.match(start_pat, l))
    j = next(k for k in range(i + 1, len(lines)) if re.match(end_pat, lines[k]))
    # also drop the docstring directly above the def
    a = i
    if lines[a - 1].strip().endswith("-/"):
        while not lines[a - 1].lstrip().startswith("/--"): a -= 1
        a -= 1
    return "\n".join(lines[:a] + lines[j:]), "\n".join(lines[a:j])
MAIN = {
  "A361711": dict(target="FormalConjectures.OEIS.Auto.«361711_10bc62a7»", thm="A361711_conjecture",
                  defstart=r"^def A361711 ", defend=r"^namespace Bala", drop_a_zero=False),
  "A364175": dict(target="FormalConjectures.OEIS.Auto.«364175_1518df7a»", thm="oeis_364175_conjecture_0",
                  defstart=r"^noncomputable def a ", defend=r"^namespace Bala", drop_a_zero=True),
  "A364178": dict(target="FormalConjectures.OEIS.Auto.«364178_4c681d65»", thm="oeis_364178_conjecture_0",
                  defstart=r"^noncomputable def a ", defend=r"^namespace Bala", drop_a_zero=False),
}
for name, c in MAIN.items():
    s = ren((SRC / f"{name}.lean").read_text())
    s = s.replace("import Mathlib\n", f"import Mathlib\nimport {c['target']}\n", 1)
    s, removed = cut(s, c["defstart"], c["defend"])
    print(f"--- {name}: removed copied definition ({removed.count(chr(10))+1} lines), first line: {removed.splitlines()[1] if removed.startswith('/--') else removed.splitlines()[0]}")
    if c["drop_a_zero"]:
        pat = "open Bala in\ntheorem a_zero : a 0 = 1 := by\n  rw [a_eq_B175]\n  decide\n"
        assert s.count(pat) == 1; s = s.replace(pat, ""); print(f"--- {name}: removed our a_zero (the target module defines a_zero)")
    n = s.count(f"theorem {c['thm']} ")
    assert n == 1, (name, n)
    s = s.replace(f"theorem {c['thm']} ", f"theorem {c['thm']}' ", 1)
    s = s.rstrip("\n") + f"\n\n/-- The statement is taken from the unmodified target module. -/\ntheorem {name}_from_target : type_of% @{c['thm']} := {c['thm']}'\n"
    (DST / f"{name}.lean").write_text(s); print(f"--- {name}: final theorem renamed {c['thm']}' ; added {name}_from_target")
