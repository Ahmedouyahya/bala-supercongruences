"""Gate runner for the Lean machine checks (protocol: verification/lean-checks/PROTOCOL.md).
usage: python3 -I gates.py <workspace> <proof module> <audit file> <theorem>[,<theorem>...] [--expect-reject]
Runs: build of the proof module (log scanned for sorry and errors); the audit file (axioms of each named theorem
must be a subset of {propext, Classical.choice, Quot.sound}, matched by exact name); a word-boundary grep of the
proof module and every BalaCheck module it imports for tampering keywords; lean4checker on those modules.
Every step prints PASS or REJECT; the summary line is the verdict."""
import os, re, subprocess, sys, json
ws, mod, audit, names = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].split(",")
expect_reject = "--expect-reject" in sys.argv
ELAN = os.path.expanduser("~/.elan/bin")
env = dict(os.environ, PATH=ELAN + ":" + os.environ["PATH"])
CAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=4G", "nice", "-n", "10"]
STD = {"propext", "Classical.choice", "Quot.sound"}
KEYWORDS = ["sorry", "admit", "axiom", "native_decide", "ofReduceBool", "implemented_by", "extern", "unsafe",
            "skipKernelTC", "macro", "elab", "syntax", "notation", "instance", "set_option", "run_cmd", "run_elab",
            "run_meta", "#eval", "#exit", "initialize", "import Lean", "modifyEnv", "addDecl", "opaque", "csimp",
            "attribute", "scoped", "local", "private"]
verdicts = []
def step(name, ok, detail=""):
    verdicts.append(ok); print(("PASS  " if ok else "REJECT") + f" {name}" + (f": {detail}" if detail else ""))
def run(cmd):
    p = subprocess.run(CAP + cmd, cwd=ws, env=env, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr

rc, log = run(["lake", "build", mod])
open(os.path.join(ws, f".gate-build-{mod}.log"), "w").write(log)
step("build exit 0", rc == 0, f"exit {rc}")
step("no sorry in build log", not re.search(r"declaration uses .sorry", log))
step("no error in build log", not re.search(r"\berror\b", log))

rc, out = run(["lake", "env", "lean", audit])
open(os.path.join(ws, f".gate-audit-{os.path.basename(audit)}.log"), "w").write(out)
step("audit file exit 0", rc == 0, f"exit {rc}")
for n in names:
    m = re.search(r"^'" + re.escape(n) + r"' depends on axioms: \[([^\]]*)\]", out, re.M)
    none = re.search(r"^'" + re.escape(n) + r"' does not depend on any axioms", out, re.M)
    if none:
        step(f"axioms of {n}", True, "none")
    elif m:
        ax = {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}
        step(f"axioms of {n}", ax <= STD, ", ".join(sorted(ax)))
    else:
        step(f"axioms of {n}", False, "no axiom line for this exact name")

# closure of BalaCheck modules imported by the proof module
def path_of(m): return os.path.join(ws, *m.split(".")) + ".lean"
todo, seen = [mod], []
while todo:
    m = todo.pop()
    if m in seen or not os.path.exists(path_of(m)): continue
    seen.append(m)
    for line in open(path_of(m), encoding="utf-8"):
        mm = re.match(r"\s*import\s+(BalaCheck\.[\w.«»]+)", line)
        if mm: todo.append(mm.group(1))
hits = []
for m in seen:
    text = open(path_of(m), encoding="utf-8").read()
    # blank out comments but keep every newline, so reported line numbers are the file's own line numbers
    text_nc = re.sub(r"/-.*?-/", lambda x: re.sub(r"[^\n]", " ", x.group(0)), text, flags=re.S)
    text_nc = re.sub(r"--[^\n]*", lambda x: " " * len(x.group(0)), text_nc)
    for kw in KEYWORDS:
        pat = re.escape(kw) if not kw[0].isalnum() else r"(?<![\w.])" + re.escape(kw) + r"(?![\w])"
        for mt in re.finditer(pat, text_nc):
            line = text_nc.count("\n", 0, mt.start()) + 1
            hits.append(f"{m}:{line}:{kw}")
allow_path = os.path.join(ws, "BalaCheck", "GREP-ALLOW.txt")
allowed = set()
if os.path.exists(allow_path):
    for line in open(allow_path, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            allowed.add(line.split()[0])          # "module:line:keyword  justification"
unapproved = [h for h in hits if h not in allowed]
print("GREP modules:", ", ".join(seen))
print("GREP hits:", len(hits), "| approved in GREP-ALLOW.txt:", len(hits) - len(unapproved))
for h in unapproved: print("   UNAPPROVED", h)
step("tamper grep: every hit reviewed and approved", not unapproved, f"{len(unapproved)} unapproved of {len(hits)}")

l4c = os.environ.get("LEAN4CHECKER", "lean4checker")
for m in seen:
    rc, out = run(["lake", "env", l4c, m])
    step(f"lean4checker {m}", rc == 0, f"exit {rc}; " + out.strip().splitlines()[-1][:120] if out.strip() else f"exit {rc}")

ok = all(verdicts)
print("VERDICT:", "ACCEPT" if ok else "REJECT", "(expected REJECT)" if expect_reject else "")
sys.exit(0 if (ok != expect_reject) else 1)
