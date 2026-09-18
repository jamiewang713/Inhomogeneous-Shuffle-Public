"""Recheck existing input packages in isolated snapshots; author no Lean source."""

from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[3]
AUDIT = Path(__file__).resolve().parent
PACKAGES = {
    "first_moment": {
        "root": ROOT / "formalization/first_moment",
        "lean": ROOT / "formalization/.tooling/lean-4.19.0-darwin_aarch64/bin/lean",
        "mathlib": ROOT / "formalization/.tooling/mathlib",
        "module": "FirstMoment",
    },
    "foundations": {
        "root": ROOT / "formalization/foundations",
        "lean": ROOT / "formalization/.tools/lean/bin/lean",
        "mathlib": ROOT / "formalization/.lake/packages/mathlib",
        "module": "RiffleShuffle",
    },
}
PACKAGES["first_moment_4_33_1"] = {
    **PACKAGES["first_moment"],
    "lean": PACKAGES["foundations"]["lean"],
    "mathlib": PACKAGES["foundations"]["mathlib"],
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(name):
    cfg = PACKAGES[name]
    package = cfg["root"]
    snapshot = Path(tempfile.mkdtemp(prefix=f"upper-input-{name}-"))
    build = snapshot / "build"
    build.mkdir()
    source_files = sorted((package / cfg["module"]).rglob("*.lean"))
    source_files += [package / f'{cfg["module"]}.lean', package / "Audit.lean"]
    sources = {}
    for source in source_files:
        rel = source.relative_to(package)
        data = source.read_bytes()
        target = snapshot / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        sources[rel.as_posix()] = {"sha256": digest(data)}

    modules = {str(Path(rel).with_suffix("")).replace("/", "."): rel for rel in sources}
    dependencies = {}
    for module, rel in modules.items():
        imported = re.findall(r"^import\s+([^\n]+)", (snapshot / rel).read_text(), re.M)
        dependencies[module] = {
            word for line in imported for word in line.split() if word in modules
        }
    order = []
    while len(order) < len(modules):
        ready = sorted(m for m in modules if m not in order and dependencies[m] <= set(order))
        if not ready:
            raise RuntimeError("Local source import cycle")
        order.extend(ready)

    mathlib = cfg["mathlib"]
    search_paths = [build, mathlib / ".lake/build/lib/lean"]
    for package_root in [mathlib / ".lake/packages", mathlib.parent]:
        search_paths.extend(sorted(package_root.glob("*/.lake/build/lib/lean")))
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(dict.fromkeys(str(p.resolve()) for p in search_paths))
    version = subprocess.check_output([str(cfg["lean"]), "--version"], text=True).strip()
    records = []
    logs = []
    for module in order:
        rel = modules[module]
        output = build / Path(rel).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        run = subprocess.run(
            [str(cfg["lean"]), "-o", str(output), rel],
            cwd=snapshot,
            env=env,
            capture_output=True,
            text=True,
            timeout=180,
        )
        transcript = run.stdout + run.stderr
        logs.append(f"MODULE {module}\n{transcript}")
        record = {"module": module, "exit_code": run.returncode,
                  "seconds": round(time.monotonic() - start, 3)}
        records.append(record)
        print(json.dumps({"package": name, **record}), flush=True)
        if run.returncode:
            break

    transcript = "\n".join(logs)
    audit_log = AUDIT / f"{name}-revalidation-build.log"
    audit_log.write_text(transcript)
    expected_audits = len(re.findall(r"^#print axioms ", (snapshot / "Audit.lean").read_text(), re.M))
    axiom_lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", transcript)
    no_axioms = re.findall(r"does not depend on any axioms", transcript)
    axiom_names = sorted({token.strip() for group in axiom_lists for token in group.split(",") if token.strip()})
    unexpected = sorted(set(axiom_names) - {"propext", "Classical.choice", "Quot.sound"})
    for rel, info in sources.items():
        info["unchanged_at_end"] = digest((package / rel).read_bytes()) == info["sha256"]
    result = {
        "package": name,
        "lean_version": version,
        "snapshot": str(snapshot),
        "source_files": sources,
        "builds": records,
        "all_compiled": len(records) == len(order) and all(r["exit_code"] == 0 for r in records),
        "audited_declarations_expected": expected_audits,
        "audited_declarations_observed": len(axiom_lists) + len(no_axioms),
        "axiom_dependencies": axiom_names,
        "unexpected_axiom_dependencies": unexpected,
        "log": str(audit_log.relative_to(ROOT)),
        "scope": "Existing declarations only; no model-first-moment or upper-bound completion inferred.",
    }
    (AUDIT / f"{name}-revalidation-build.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    import sys
    check(sys.argv[1])
