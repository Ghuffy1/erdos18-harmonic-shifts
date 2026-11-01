"""Compile local modules against existing, read-only mathlib dependencies."""
import argparse
import hashlib
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import re
import subprocess
import time
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("module", nargs="*")
parser.add_argument("--all", action="store_true", help="Compile every local module in dependency order")
parser.add_argument("--fresh", action="store_true", help="Use a new empty local output directory")
parser.add_argument("--build-dir", type=Path)
parser.add_argument("--trust-zero", action="store_true", help="Ask Lean to recheck imported declarations")
parser.add_argument("--resume", action="store_true", help="Resume a stopped fresh build after validating completed outputs")
parser.add_argument("--dependency-project", type=Path, default=ROOT / "lean")
parser.add_argument("--lean", default=shutil.which("lean"), help="Lean 4.34.0 executable")
parser.add_argument("--timeout", type=int, default=90)
parser.add_argument("--memory-mb", type=int, default=2048)
args = parser.parse_args()
if not args.lean:
    parser.error("Lean executable not found; use --lean")
dep = Path(args.dependency_project)
build = args.build_dir or (Path(tempfile.mkdtemp(prefix=".verify-", dir=ROOT / "lean"))
                          if args.fresh else ROOT / "lean" / ".build")
build = build.resolve()
logs = ROOT / "verification"
build.mkdir(exist_ok=True)
logs.mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join([str(build)] + [
    str(d / ".lake" / "build" / "lib" / "lean")
    for d in (dep / ".lake" / "packages").iterdir() if d.is_dir()
])
sources = {".".join(p.relative_to(ROOT / "lean").with_suffix("").parts): p
           for p in (ROOT / "lean").rglob("*.lean")
           if not any(part.startswith(".") for part in p.relative_to(ROOT / "lean").parts)}
modules = []
visited = set()
def visit(module):
    if module in visited:
        return
    visited.add(module)
    for dependency in re.findall(r"^import\s+(Erdos18c(?:\.[A-Za-z0-9_]+)?)\s*$",
                                 sources[module].read_text(encoding="utf-8"), re.M):
        visit(dependency)
    modules.append(module)
if args.all:
    for module in sorted(sources):
        visit(module)
else:
    modules = args.module
if not modules:
    parser.error("Specify module names or --all")
run = dict(started_at=datetime.now(timezone.utc).isoformat(), build_dir=str(build),
           fresh_local_outputs=args.fresh, trust_zero=args.trust_zero, modules=modules, completed=[])
run_file = logs / ("trust-zero-run.json" if args.trust_zero else "clean-build.json")
if args.resume:
    assert args.all and args.build_dir and not args.fresh and not args.trust_zero
    run=json.loads(run_file.read_text(encoding="utf-8"))
    assert Path(run['build_dir']).resolve()==build.resolve()
    assert run['modules']==modules
    for done in run['completed']:
        rec=json.loads((logs/(done+'.json')).read_text(encoding='utf-8'))
        out=Path(rec['command'][rec['command'].index('-o')+1])
        assert rec['exit_code']==0
        assert rec['source_sha256']==hashlib.sha256(sources[done].read_bytes()).hexdigest()
        assert rec['output_sha256']==hashlib.sha256(out.read_bytes()).hexdigest()
    run.setdefault('resumed_at',[]).append(datetime.now(timezone.utc).isoformat())
    modules=modules[len(run['completed']):]
if args.all or args.trust_zero:
    run_file.write_text(json.dumps(run, indent=2)+"\n", encoding="utf-8")
for module in modules:
    source = ROOT / "lean" / Path(*module.split(".")).with_suffix(".lean")
    if not source.is_file():
        raise FileNotFoundError(source)
    output = build / Path(*module.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [args.lean, f"--memory={args.memory_mb}", "-j1",
               f"--root={ROOT / 'lean'}", "-o", str(output), str(source)]
    if args.trust_zero:
        command.insert(1, "--trust=0")
    t = time.monotonic()
    try:
        result = subprocess.run(command, cwd=ROOT / "lean", env=env,
                                capture_output=True, timeout=args.timeout,
                                encoding="utf-8", errors="replace")
        code, stdout, stderr, timeout = result.returncode, result.stdout, result.stderr, False
    except subprocess.TimeoutExpired as e:
        code, stdout, stderr, timeout = None, str(e.stdout or ""), str(e.stderr or ""), True
    record = dict(module=module, command=command, dependency_project=str(dep),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  checked_at=datetime.now(timezone.utc).isoformat(),
                  elapsed_seconds=round(time.monotonic()-t, 3), exit_code=code,
                  timeout=timeout, timeout_seconds=args.timeout, memory_mb=args.memory_mb,
                  stdout=stdout, stderr=stderr,
                  full_erdos18c_verification=False, trust_zero=args.trust_zero,
                  scope="This record covers the named module only.")
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", stdout)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    record["axiom_audits"] = {
        name: [x.strip() for x in names.split(",") if x.strip()]
        for name, names in audits
    }
    record["axiom_audits_standard_only"] = all(
        set(names) <= allowed for names in record["axiom_audits"].values())
    record["full_erdos18c_verification"] = (code == 0 and
        record["axiom_audits_standard_only"] and "Erdos18.erdos_18c" in record["axiom_audits"])
    if code == 0 and output.exists():
        record["output_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
    suffix = ".trust-zero.json" if args.trust_zero else ".json"
    (logs / (module + suffix)).write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: record[key] for key in
        ("module", "checked_at", "elapsed_seconds", "exit_code", "timeout", "axiom_audits_standard_only")}
        | {"diagnostics": stdout if code != 0 else "Saved in verification receipt",
           "stderr": stderr}), flush=True)
    if code != 0 or not record["axiom_audits_standard_only"]:
        raise SystemExit(1)
    run["completed"].append(module)
    if args.all or args.trust_zero:
        run["finished_at"] = datetime.now(timezone.utc).isoformat()
        run["all_modules_passed"] = len(run["completed"]) == len(run["modules"])
        run_file.write_text(json.dumps(run, indent=2)+"\n", encoding="utf-8")
