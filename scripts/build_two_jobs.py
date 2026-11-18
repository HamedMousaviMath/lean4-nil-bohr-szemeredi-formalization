"""Build project modules in dependency order, with at most two active checks."""

from pathlib import Path
import re
import subprocess


def project_imports(source):
    return set(re.findall(r"^import (NilBohr\.\S+)", source.read_text(), re.M))


pending = {f"NilBohr.{source.stem}": project_imports(source)
           for source in sorted(Path("NilBohr").glob("*.lean"))}
while pending:
    ready = [module for module, imports in pending.items()
             if imports.isdisjoint(pending)][:2]
    if not ready:
        raise SystemExit(f"Cycle in project imports: {', '.join(pending)}")
    subprocess.run(["lake", "build", *ready], check=True)
    for module in ready:
        del pending[module]

subprocess.run(["lake", "build"], check=True)
