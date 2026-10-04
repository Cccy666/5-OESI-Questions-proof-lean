"""Build all five Lean proofs and audit final theorem dependencies."""
from pathlib import Path
import argparse
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDITS = [
    ("OEISOpen/A006343/Audit.lean", "OEISOpen.A006343.recurrence_of_algebraic"),
    ("OEISOpen/A089073/Audit.lean", "OEISOpen.A089073.a089073_recurrence"),
    ("OEISOpen/A150500/Audit.lean", "OEISOpen.A150500.a150500_recurrence"),
    ("OEISOpen/A219692/Audit.lean", "OEISOpen.A219692.original_tail_recurrence"),
    ("OEISOpen/A371753/formal/Check.lean", "OEISOpen.A371753.recurrence"),
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-only", action="store_true",
                        help="Audit existing build artifacts without rebuilding them")
    args = parser.parse_args()
    if not args.audit_only:
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    for source, target in AUDITS:
        run = subprocess.run(["lake", "env", "lean", source], cwd=ROOT,
                             capture_output=True, text=True, encoding="utf-8", errors="replace")
        text = run.stdout + run.stderr
        if run.returncode or "sorryAx" in text or "declaration uses 'sorry'" in text:
            print(text)
            raise RuntimeError(f"Lean audit failed: {source}")
        rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
        dependencies = {name: {a.strip() for a in axioms.split(",") if a.strip()}
                        for name, axioms in rows}
        if target not in dependencies:
            raise RuntimeError(f"Missing final theorem audit: {target}")
        unexpected = set().union(*dependencies.values()) - ALLOWED
        if unexpected:
            raise RuntimeError(f"Unexpected axioms: {sorted(unexpected)}")
        print(f"PASS {target}: {sorted(dependencies[target])}", flush=True)
    print("PASS: all five final theorem audits")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
