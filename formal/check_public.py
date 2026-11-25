"""Check the public import closure in a single Lean process at a time."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".lake" / "checked-public"
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(Erdos272\.[\w.]+)", re.M)
ARTIFACT_SUFFIXES = (".ir", ".ir.sig", ".olean.private", ".olean.server", ".olean")


def check_public(memory):
    if "LEAN_PATH" not in os.environ:
        raise SystemExit("Run from formal with: lake env python check_public.py")
    lean_version = subprocess.check_output(["lean", "--version"], cwd=ROOT)
    manifest = (ROOT / "lake-manifest.json").read_bytes()
    config_hash = sha256(lean_version + manifest).digest()

    artifacts = CACHE / "lib"
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    env["LEAN_PATH"] = os.pathsep.join((str(artifacts), env["LEAN_PATH"]))
    fingerprints = {}
    rebuilt = 0

    def check(module):
        nonlocal rebuilt
        if module in fingerprints:
            return fingerprints[module]

        relative = Path(*module.split("."))
        source = relative.with_suffix(".lean")
        contents = (ROOT / source).read_bytes()
        deps = IMPORT.findall(contents.decode("utf-8"))
        signature = sha256(config_hash + contents + b"".join(check(dep) for dep in deps)).digest()
        olean = (artifacts / relative).with_suffix(".olean")
        trace = olean.with_suffix(".source-sha256")
        fresh = (
            olean.exists()
            and trace.exists()
            and trace.read_text(encoding="ascii") == signature.hex()
        )

        # Re-elaborate the public file so its theorem types and axioms are printed.
        if not fresh or module == "PublicResults":
            olean.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {module}", flush=True)
            with TemporaryDirectory(prefix="lean-", dir=CACHE) as directory:
                staged = Path(directory) / olean.name
                subprocess.run(
                    ["lean", "-j1", f"-M{memory}", "-o", str(staged), str(source)],
                    cwd=ROOT,
                    env=env,
                    check=True,
                )
                for suffix in ARTIFACT_SUFFIXES:
                    artifact = staged.with_suffix(suffix)
                    destination = olean.with_suffix(suffix)
                    if artifact.exists():
                        artifact.replace(destination)
                    else:
                        destination.unlink(missing_ok=True)
            trace.write_text(signature.hex(), encoding="ascii")
            rebuilt += 1

        fingerprints[module] = signature
        return signature

    print(lean_version.decode("utf-8").strip(), flush=True)
    check("PublicResults")
    print(f"Checked {len(fingerprints)} project modules, elaborated {rebuilt}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--memory", type=int, default=4096, metavar="MIB",
                        help="Lean memory setting passed to lean -M (default 4096)")
    args = parser.parse_args()
    if args.memory <= 0:
        parser.error("--memory must be positive")
    check_public(args.memory)
