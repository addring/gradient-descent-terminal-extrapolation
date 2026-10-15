"""Compile the development extension and report every remaining proof hole.

This uses an existing ASCII staging checkout with the pinned dependency cache.
It does not certify proofs when the audit contains sorryAx.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--skip-unchanged", action="store_true")
    parser.add_argument("--combined", action="store_true",
                        help="Check all development declarations and their audit in one Lean invocation.")
    parser.add_argument("--interfaces-only", action="store_true",
                        help="Validate statement types only, replacing proof bodies in the generated check.")
    parser.add_argument("--copy-dependencies", action="store_true")
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1] / "lean_formalization"
    stage = args.stage.resolve()
    if stage == project.resolve():
        parser.error("Use a separate ASCII staging checkout.")
    libs = stage / ".lake" / "build" / "lib" / "lean"
    existing_libs = project / ".lake" / "build" / "lib" / "lean"
    if args.copy_dependencies:
        for package in (project / ".lake" / "packages").iterdir():
            cache = package / ".lake" / "build" / "lib" / "lean"
            if cache.is_dir():
                print(f"Copying dependency cache {package.name}", flush=True)
                target = stage / "deps" / package.name / ".lake" / "build" / "lib" / "lean"
                if os.name == "nt" and shutil.which("robocopy"):
                    copied = subprocess.run(["robocopy", str(cache), str(target), "/E", "/MT:16",
                                             "/NFL", "/NDL", "/NJH", "/NJS", "/NP", "/R:0", "/W:0"])
                    if copied.returncode >= 8:
                        raise RuntimeError(f"Dependency cache copy failed: {package.name}")
                else:
                    shutil.copytree(cache, target, dirs_exist_ok=True)
    if args.prepare_only:
        return 0
    packages = stage / "deps"
    if not packages.is_dir():
        packages = stage / ".lake" / "packages"
    if not packages.is_dir():
        packages = project / ".lake" / "packages"
    if not (existing_libs / "PaperFramework" / "CriticalInterval.olean").is_file():
        parser.error("The project needs its compiled existing library and pinned dependencies.")
    libs.mkdir(parents=True, exist_ok=True)
    (libs / "PaperFramework").mkdir(exist_ok=True)
    for baseline in existing_libs.rglob("*.olean"):
        cached = libs / baseline.relative_to(existing_libs)
        if not cached.is_file():
            cached.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(baseline, cached)
    names = ["OriginalFeasibility", "OriginalEnergy", "OriginalQuadratic",
             "OriginalObjective", "OriginalCritical"]
    sources = [Path("PaperFramework") / f"{n}.lean" for n in names]
    sources.extend([Path("OriginalExtension.lean"), Path("OriginalAudit.lean")])
    output_dir = project / "verification" / "original_extension"
    if args.interfaces_only:
        if not args.combined:
            parser.error("--interfaces-only requires --combined")
        output_dir = output_dir / "interfaces"
    output_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    paths = [libs]
    paths += [p / ".lake" / "build" / "lib" / "lean" for p in packages.iterdir() if p.is_dir()]
    env["LEAN_PATH"] = os.pathsep.join(p.as_posix() for p in paths)
    source_manifest = [{"file": rel.as_posix(), "sha256": hashlib.sha256((project / rel).read_bytes()).hexdigest()}
                       for rel in sources]
    units = [(rel, (project / rel).read_bytes()) for rel in sources]
    if args.combined:
        external_imports = []
        for _, raw in units:
            for name in re.findall(r"(?m)^import ([^\r\n]+)", raw.decode("utf-8")):
                if not name.startswith("PaperFramework.Original") and name != "OriginalExtension":
                    if name not in external_imports:
                        external_imports.append(name)
        if args.interfaces_only:
            external_imports = ["PaperFramework.Definitions", "PaperFramework.TrialFunctional"]
        content = "".join(f"import {name}\n" for name in external_imports) + "\n"
        for rel, raw in units:
            content += f"\n/- Source: {rel.as_posix()} -/\n"
            body = re.sub(r"(?m)^import [^\r\n]+\r?\n", "", raw.decode("utf-8"))
            if args.interfaces_only:
                def stub(match):
                    block = match.group(0)
                    boundary = block.index(":= by") + len(":= by")
                    return block[:boundary] + "\n  sorry\n\n"
                body = re.sub(r"(?m)^theorem\s+\w+\b.*?(?=^theorem\s|^/--|^end\s*$)",
                              stub, body, flags=re.S)
            content += body
            content += "\n"
        combined_name = "CombinedOriginalInterfaces.lean" if args.interfaces_only else "CombinedOriginal.lean"
        units = [(Path(combined_name), content.encode("utf-8"))]
        # Preserve exactly the bytes compiled below, including mixed source newlines.
        (output_dir / combined_name).write_bytes(content.encode("utf-8"))
    records = []
    log_path = output_dir / "framework_build.log"
    (output_dir / "framework_status.json").write_text(json.dumps({
        "status": "running", "proof_complete": False,
        "modules": [],
    }, indent=2) + "\n", encoding="utf-8")
    dirty = False
    with log_path.open("w", encoding="utf-8") as log:
        for rel, raw in units:
            dest = stage / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            same = dest.is_file() and dest.read_bytes() == raw
            if not same:
                dest.write_bytes(raw)
            olean = libs / rel.with_suffix(".olean")
            skip = (args.skip_unchanged and not dirty and same and olean.is_file()
                    and olean.stat().st_mtime >= dest.stat().st_mtime
                    and rel.name not in {"OriginalAudit.lean", "CombinedOriginal.lean", "CombinedOriginalInterfaces.lean"})
            print(f"{'Cached' if skip else 'Checking'} {rel.as_posix()}", flush=True)
            command = [str(args.lean), "--profile", "-DautoImplicit=false", "-DmaxHeartbeats=800000",
                       f"--root={stage.as_posix()}"]
            if rel.name != "OriginalAudit.lean":
                command += ["-o", olean.as_posix()]
            command += [dest.as_posix()]
            log.write(f"\nFILE {rel.as_posix()}\n")
            log.flush()
            if skip:
                code, content = 0, "unchanged staging compilation reused\n"
            else:
                dirty = True
                proc = subprocess.Popen(command, cwd=stage, env=env,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, encoding="utf-8", errors="replace")
                chunks = []
                for line in proc.stdout:
                    chunks.append(line)
                    print(line, end="", flush=True)
                    log.write(line)
                    log.flush()
                code, content = proc.wait(), "".join(chunks)
            if skip:
                log.write(content)
            log.write("\n")
            log.flush()
            if skip:
                print(content, end="", flush=True)
            records.append({"file": rel.as_posix(), "exit_code": code,
                            "sha256": hashlib.sha256(raw).hexdigest(), "cached": skip})
            if code:
                break
    source_holes = []
    for rel in sources:
        for line, text in enumerate((project / rel).read_text(encoding="utf-8").splitlines(), 1):
            if re.match(r"\s*sorry\s*$", text):
                source_holes.append({"file": rel.as_posix(), "line": line})
    log_text = log_path.read_text(encoding="utf-8")
    audit_ran = len(records) == len(units) and records[-1]["exit_code"] == 0
    has_sorry_axiom = audit_ran and "sorryAx" in log_text
    expected = {"CriticalExtrapolation.Paper." + name for rel in sources
                for name in re.findall(r"(?m)^theorem\s+(\w+)",
                                       (project / rel).read_text(encoding="utf-8"))}
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                         log_text)
    audited = {name for name, _ in entries}
    axioms = {item.strip() for _, row in entries for item in row.split(",") if item.strip()}
    unexpected = sorted(axioms - {"propext", "Classical.choice", "Quot.sound", "sorryAx"})
    audit_complete = audit_ran and expected == audited
    status = {
        "status": ("interfaces_compile" if args.interfaces_only else "framework_compiles") if audit_ran else "compilation_failed",
        "proof_complete": bool(not args.interfaces_only and audit_complete and not source_holes and not has_sorry_axiom and not unexpected),
        "sorry_count": len(source_holes), "sorry_locations": source_holes,
        "audit_contains_sorryAx": has_sorry_axiom if audit_ran else None,
        "audit_complete": audit_complete, "audited_theorems": len(audited),
        "unexpected_axioms": unexpected,
        "combined": args.combined, "interfaces_only": args.interfaces_only, "source_manifest": source_manifest,
        "modules": records,
    }
    (output_dir / "framework_status.json").write_text(
        json.dumps(status, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in status.items()
                      if k not in {"modules", "sorry_locations", "source_manifest"}}), flush=True)
    return 0 if audit_ran and (args.interfaces_only or status["proof_complete"]) else 1


if __name__ == "__main__":
    sys.exit(main())
