"""Checks that every definition and the conjecture statement of each benchmark target in
statements/lean-targets/ occur verbatim (character for character) in the repository's Lean files.

For each target, the definition blocks (top-level `def`, `noncomputable def`, `abbrev`, each with its
docstring) and the conjecture theorem's docstring and statement (up to `:= by`) are extracted and searched
for in the concatenation of the entry's files in lean/BalaProofs/. Usage, from the repository root:
    python3 -I verification/lean-statement-check/verbatim_check.py
"""
import pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
TGT = ROOT / "statements/lean-targets"
LEAN = ROOT / "lean/BalaProofs"
ENTRIES = {  # entry: (target file, conjecture theorem, repository files holding definitions and statement)
    "A333561": ("333561_b286c526", "oeis_333561_conjecture", ["A333561Defs", "A333561"]),
    "A333562": ("333562_2eccaf4c", "oeis_333562_conjecture_0_congruence", ["A333562Defs", "A333562"]),
    "A333565": ("333565_757e3efd", "oeis_A333565_conjecture_strong_gauss_congruence", ["A333565Defs", "A333565"]),
    "A352275": ("352275_4b1f2230", "u_m_supercongruence_conjecture", ["A352275"]),
    "A352373": ("352373_a1d5fa75", "oeis_a352373_supercongruence", ["A352373Defs", "A352373"]),
    "A361711": ("361711_10bc62a7", "A361711_conjecture", ["A361711"]),
    "A363983": ("363983_3f7e4c53", "oeis_A363983_conjecture_supercongruence", ["A363983Defs", "A363983"]),
    "A364175": ("364175_1518df7a", "oeis_364175_conjecture_0", ["A364175"]),
    "A364178": ("364178_4c681d65", "oeis_364178_conjecture_0", ["A364178"]),
    "A370092": ("370092_862cfcda", "oeis_370092_conjecture_0", ["A370092Defs", "A370092"]),
    "A376462": ("376462_96154f2f", "oeis_376462_conjecture_0", ["A376462Defs", "A376462"]),
    "A386548": ("386548_8788c4f8", "oeis_A386548_supercongruence_conjecture", ["A386548Defs", "A386548"]),
}
TOP = re.compile(r"^(/--|theorem |lemma |def |noncomputable def |abbrev |open |namespace |end |section |@\[|example |instance |#)", re.M)

def blocks(src):
    """Top-level items, each with a preceding docstring if any."""
    starts = [m.start() for m in TOP.finditer(src)] + [len(src)]
    items, pending = [], None
    for a, b in zip(starts, starts[1:]):
        chunk = src[a:b].rstrip()
        # a comment line between two items belongs to neither
        while chunk.rsplit("\n", 1)[-1].lstrip().startswith("--"):
            chunk = chunk.rsplit("\n", 1)[0].rstrip()
        if chunk.startswith("/--") and chunk.endswith("-/"):
            pending = chunk; continue
        items.append((pending + "\n" + chunk) if pending else chunk); pending = None
    return items

fails = 0
for e, (t, thm, files) in ENTRIES.items():
    tsrc = (TGT / f"{t}.lean").read_text()
    rsrc = "\n".join((LEAN / f"{f}.lean").read_text() for f in files)
    want = []
    for it in blocks(tsrc):
        head = it[it.index("-/") + 3:] if it.startswith("/--") else it
        if re.match(r"(noncomputable def|def|abbrev) ", head):
            want.append(("definition " + head.split()[1 if head.startswith(("def", "abbrev")) else 2], it))
        elif head.startswith(("theorem " + thm, "lemma " + thm)):
            m = re.search(r":=\s*by\b", it)
            want.append(("statement " + thm, it[: m.start()] if m else it))
    names = [w[0] for w in want]
    missing = [n for n, s in want if s not in rsrc]
    if not any(n.startswith("statement") for n in names):
        missing.append("statement " + thm + " (not found in target)")
    status = "OK" if not missing else "MISMATCH"
    fails += bool(missing)
    print(f"{e}: {status}; checked {', '.join(names)}" + (f"; not verbatim: {', '.join(missing)}" if missing else ""))
print("all verbatim" if not fails else f"{fails} entries with differences")
sys.exit(1 if fails else 0)
