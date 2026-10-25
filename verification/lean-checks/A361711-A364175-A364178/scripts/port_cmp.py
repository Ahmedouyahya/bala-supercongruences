"""Comparator layout for A361711, A364175, A364178 (cmp-ws, Lean v4.27.0).
Submission/Old/<helper>.lean : the fc-ws port of each helper (imports BalaCheck.Old.X -> Submission.Old.X).
Submission/<N>Full.lean      : the repository proof file (imports renamed; one logged v4.27 rename lives in the helper),
                               definition verbatim, final theorem renamed <thm>_full.
Submission/<N>Spec.lean      : the official theorem name with the repository statement, proved by <thm>_full.
Submission/<N>NegWeak.lean   : control: the official name with a weaker modulus (exponent minus 1), proved from <thm>_full;
                               Comparator must reject it."""
import pathlib, re
import os
REPO = pathlib.Path(__file__).resolve().parents[4]  # repository root
SRC = REPO / "lean/BalaProofs"
FCOLD = pathlib.Path(os.environ["BALA_CHECK_DIR"]) / "fc-ws/BalaCheck/Old"
SUB = pathlib.Path(os.environ["BALA_CHECK_DIR"]) / "cmp-ws/Submission"
(SUB / "Old").mkdir(exist_ok=True)
for f in FCOLD.glob("*.lean"):
    if f.stem in ("A361711", "A364175", "A364178"): continue
    (SUB / "Old" / f.name).write_text(f.read_text().replace("import BalaCheck.Old.", "import Submission.Old."))
    print("helper", f.stem)
E = {"A361711": ("A361711_conjecture", "p hp h_geq_5 k hk", "(3 * k)", "(3 * k - 1)",
                 "Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow _ (Nat.sub_le _ _)))", "open Nat Int Finset BigOperators"),
     "A364175": ("oeis_364175_conjecture_0", "p n r hp h_prime_ge_five hn hr", "(3 * r)", "(3 * r - 1)",
                 "Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _))", ""),
     "A364178": ("oeis_364178_conjecture_0", "p n r hp h5 hn hr", "(3 * r)", "(3 * r - 1)",
                 "Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _))", "")}
for n, (thm, args, mod, weak, ofdvd, opens) in E.items():
    s = (SRC / f"{n}.lean").read_text().replace("import BalaProofs.", "import Submission.Old.")
    m = re.search(r"theorem " + thm + r" (.*?):= by", s, re.S); sig = m.group(1)
    assert s.count(f"theorem {thm} ") == 1 and sig.count(mod) == 1, n
    (SUB / f"{n}Full.lean").write_text(s.replace(f"theorem {thm} ", f"theorem {thm}_full ", 1))
    (SUB / f"{n}Spec.lean").write_text(f"import Submission.{n}Full\n\n{opens}\n\ntheorem {thm} {sig}:=\n  {thm}_full {args}\n")
    (SUB / f"{n}NegWeak.lean").write_text(f"import Submission.{n}Full\n\n{opens}\n\n-- control: weaker modulus, must be rejected by Comparator\ntheorem {thm} {sig.replace(mod, weak)}:=\n  {ofdvd} ({thm}_full {args})\n")
    print(n, "statement:", " ".join(sig.split()))
