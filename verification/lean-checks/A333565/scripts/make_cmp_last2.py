"""Comparator layouts for A376462 and A333565 (cmp-ws, Lean v4.27.0), generated from the fc-ws proof files.
<E>Defs: the official challenge cut before the theorem's docstring. Proof modules: imports BalaCheck.X -> Submission.X,
target -> Submission.<E>Defs. <E>Full: final theorem with an explicit statement (same proof); Spec: official name;
NegWeak: a true but weaker statement (A376462: second conjunct modulo p^(3r-1); A333565: modulo p^(3k-1)), must be rejected."""
import pathlib, re
import os
L = pathlib.Path(os.environ["BALA_CHECK_DIR"])
FC = L / "fc-ws/BalaCheck"; SUB = L / "cmp-ws/Submission"; ISO = pathlib.Path(os.environ["LOP_ISOLATED"])
def ren(s, tgt, E):
    s = s.replace(f"import FormalConjectures.OEIS.Auto.«{tgt}»", f"import Submission.{E}Defs")
    return re.sub(r"^import BalaCheck\.", "import Submission.", s, flags=re.M)
def defs(thm, head, E):
    ch = (ISO / f"{thm}.lean").read_text(); ti = ch.index(head); di = ch.rfind("/--", 0, ti)
    assert ch[di:ti].rstrip().endswith("-/") and "theorem" not in ch[di:ti], E
    (SUB / f"{E}Defs.lean").write_text(ch[:di].rstrip() + "\n"); return ch
# ---- A376462
E, tgt, thm = "A376462", "376462_96154f2f", "oeis_376462_conjecture_0"
ch = defs(thm, "theorem oeis_376462_conjecture_0 :", E)
stmt = ch[ch.index("theorem oeis_376462_conjecture_0 :") + len("theorem oeis_376462_conjecture_0 :"): ch.index(":= by sorry", ch.index("theorem oeis_376462_conjecture_0 :"))].rstrip()
for m in ["ShiftLibProd", "ShiftLibHarm", "ShiftLibBlock", "A376462Rep", "A376462Kernel", "A376462Classes", "A376462First",
          "A376462ShiftRep", "A376462ShiftK", "A376462ShiftJ", "A376462ShiftB", "A376462ShiftS", "A376462ShiftMain"]:
    (SUB / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text(), tgt, E))
main = ren((FC / "A376462Main.lean").read_text(), tgt, E)
old = "theorem A376462_from_target : type_of% @oeis_376462_conjecture_0 := by"; assert main.count(old) == 1
(SUB / "A376462Full.lean").write_text(main.replace(old, "theorem A376462_full :" + stmt + " := by"))
(SUB / "A376462Spec.lean").write_text("import Submission.A376462Full\n\nopen Nat Finset\n\ntheorem oeis_376462_conjecture_0 :" + stmt + " :=\n  A376462_full\n")
second = "(A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]"; assert stmt.count(second) == 1
weak = stmt.replace(second, "(A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r - 1) : ℕ).cast]")
(SUB / "A376462NegWeak.lean").write_text("import Submission.A376462Full\n\nopen Nat Finset\n\n-- control: second congruence weakened to p^(3r-1), must be rejected by Comparator\ntheorem oeis_376462_conjecture_0 :" + weak + " := by\n  intro p n r hp hp5 hn hr\n  have h := A376462_full p n r hp hp5 hn hr\n  refine ⟨h.1, ?_⟩\n  exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (Nat.sub_le _ _))) h.2\n")
print("A376462 written")
# ---- A333565
E, tgt, thm = "A333565", "333565_757e3efd", "oeis_A333565_conjecture_strong_gauss_congruence"
head = "theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :"
ch = defs(thm, head, E)
body = "(A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)]"
assert " ".join((head + " " + body).split()) in " ".join(ch.split())
for m in ["A333565Bridge", "TF3Harm", "TF3G", "TF3Exp", "TF3Main"]:
    (SUB / f"{m}.lean").write_text(ren((FC / f"{m}.lean").read_text(), tgt, E))
main = ren((FC / "A333565.lean").read_text(), tgt, E)
old = "theorem A333565_from_target : type_of% @oeis_A333565_conjecture_strong_gauss_congruence := by"; assert main.count(old) == 1
full = "theorem A333565_full :\n    ∀ (p n k : ℕ), Nat.Prime p → 3 ≤ p → n > 0 → k > 0 →\n    " + body + " := by"
(SUB / "A333565Full.lean").write_text(main.replace(old, full))
(SUB / "A333565Spec.lean").write_text("import Submission.A333565Full\n\nopen Nat Int BigOperators\n\n" + head + "\n    " + body + " :=\n  A333565_full p n k hp hp3 hn hk\n")
(SUB / "A333565NegWeak.lean").write_text("import Submission.A333565Full\n\nopen Nat Int BigOperators\n\n-- control: weaker modulus p^(3k-1), must be rejected by Comparator\n" + head + "\n    " + body.replace("(3 * k)", "(3 * k - 1)") + " :=\n  Int.ModEq.of_dvd (pow_dvd_pow _ (Nat.sub_le _ _)) (A333565_full p n k hp hp3 hn hk)\n")
print("A333565 written")
