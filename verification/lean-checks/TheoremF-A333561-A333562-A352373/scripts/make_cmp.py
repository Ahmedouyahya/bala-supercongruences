"""Comparator layout for A333561, A333562, A352373 (cmp-ws, Lean v4.27.0), generated from the fc-ws proof files.
<E>Defs: the official challenge cut before the theorem's docstring (definitions verbatim by construction).
Shared modules (EpochExp, TF*, A333562Ident): imports BalaCheck.X -> Submission.X, target -> Submission.<E>Defs.
<E>Full: the final theorem with an explicit statement (same proof); Spec: the official name; NegWeak: modulus p^(3k-1)."""
import pathlib, re
import os
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; SUB = L / "cmp-ws/Submission"; ISO = pathlib.Path(os.environ["LOP_ISOLATED"])
def ren(s, tgt=None, E=None):
    if tgt: s = s.replace(f"import FormalConjectures.OEIS.Auto.«{tgt}»", f"import Submission.{E}Defs")
    return re.sub(r"^import BalaCheck\.", "import Submission.", s, flags=re.M)
for m in ["EpochExp", "TFSetup", "TFFrob", "TFHarmonic", "TFEps", "TFLift", "TFMain", "TFInst"]:
    (SUB / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text())); print("copied", m)
ENTRIES = {
 "A333561": dict(tgt="333561_b286c526", thm="oeis_333561_conjecture", head="theorem oeis_333561_conjecture :",
   stmt="∀ (p n k : ℕ),\n    Nat.Prime p →\n    p ≥ 5 →\n    n ≥ 1 →\n    k ≥ 1 →\n    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)]",
   mod="(3 * k)]", weak="(3 * k - 1)]", spec_proof="A333561_full",
   neg_proof="fun p n k hp hp5 hn hk => Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333561_full p n k hp hp5 hn hk)", opens="open Nat Finset"),
 "A333562": dict(tgt="333562_2eccaf4c", thm="oeis_333562_conjecture_0_congruence", head="theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :",
   stmt="Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →\n    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)]",
   mod="(3 * k)]", weak="(3 * k - 1)]", spec_proof="A333562_full p n k",
   neg_proof="fun hp hp5 hn hk => Nat.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333562_full p n k hp hp5 hn hk)", opens="open Nat Finset"),
 "A352373": dict(tgt="352373_a1d5fa75", thm="oeis_a352373_supercongruence", head="theorem oeis_a352373_supercongruence :",
   stmt="∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),\n  ∀ (n : ℕ) (hn_pos : 0 < n),\n  ∀ (k : ℕ) (hk_pos : 0 < k),\n  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]",
   mod="(3 * k)]", weak="(3 * k - 1)]", spec_proof="A352373_full",
   neg_proof="fun p hp hp5 n hn k hk => Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A352373_full p hp hp5 n hn k hk)", opens="open scoped BigOperators Nat Finset Int"),
}
for E, c in ENTRIES.items():
    ch = (ISO / f"{c['thm']}.lean").read_text()
    ti = ch.index(c["head"]); di = ch.rfind("/--", 0, ti)
    assert ch[di:ti].rstrip().endswith("-/") and "theorem" not in ch[di:ti], E
    (SUB / f"{E}Defs.lean").write_text(ch[:di].rstrip() + "\n")
    full_stmt = c["stmt"] if E != "A333562" else "∀ (p n k : ℕ), " + c["stmt"]
    assert " ".join(c["stmt"].split()) in " ".join(ch[ti:].split()), f"{E}: statement text differs from challenge"
    if E == "A333562":
        (SUB / "A333562Ident.lean").write_text(ren((FC / "A333562Ident.lean").read_text(), c["tgt"], E)); print("copied A333562Ident")
    inst = ren((FC / f"{E}.lean").read_text(), c["tgt"], E)
    old = f"theorem {E}_from_target : type_of% @{c['thm']} := by"
    assert inst.count(old) == 1, E
    (SUB / f"{E}Full.lean").write_text(inst.replace(old, f"theorem {E}_full :\n    {full_stmt} := by"))
    (SUB / f"{E}Spec.lean").write_text(f"import Submission.{E}Full\n\n{c['opens']}\n\n{c['head']}\n    {c['stmt']} :=\n  {c['spec_proof']}\n")
    weak = c["stmt"].replace(c["mod"], c["weak"]); assert weak != c["stmt"]
    (SUB / f"{E}NegWeak.lean").write_text(f"import Submission.{E}Full\n\n{c['opens']}\n\n-- control: weaker modulus, must be rejected by Comparator\n{c['head']}\n    {weak} :=\n  {c['neg_proof']}\n")
    print(E, "Defs/Full/Spec/NegWeak written")
