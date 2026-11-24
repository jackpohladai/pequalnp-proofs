"""Assemble the private-reader child on a machine with Lean and the saved proof archive.

Usage from the repository root:
    python3 recovery-4223/assemble.py /path/to/Lean_Partial_Proofs_and_Search.zip /tmp/FirstChildProof.lean
    (cd lean && lake env lean /tmp/FirstChildProof.lean)

The original full child compiled with only PEqualNP.Defs and passed leanchecker.
Its masked-prefix induction was reconstructed after the original workspace stopped.
Run both Lean checks again before submitting the assembled module.
"""
import argparse
from pathlib import Path
from zipfile import ZipFile

PARTS = Path(__file__).resolve().parent

def archived_source(path, filename):
    if path.is_dir():
        names = [p for p in path.rglob(filename) if p.is_file()]
        if len(names) != 1:
            raise ValueError(f"Expected one {filename} under {path}, found {names}")
        return names[0].read_text(encoding="utf-8")
    with ZipFile(path) as archive:
        matches = [p for p in archive.namelist() if Path(p).name == filename]
        if len(matches) != 1:
            raise ValueError(f"Expected one {filename} in {path}, found {matches}")
        return archive.read(matches[0]).decode("utf-8")

def initial_part(text, marker):
    if marker not in text:
        raise ValueError(f"Missing expected source anchor {marker!r}")
    return text.split(marker, 1)[0]

def from_marker(text, marker):
    if marker not in text:
        raise ValueError(f"Missing expected source anchor {marker!r}")
    return text[text.index(marker):]

def block(text, start, end):
    return initial_part(from_marker(text, start), end)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("archive_or_directory", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--theorem-name", default="PetersenPositivePartner.provedChild",
                   help="For a published child, supply its exact PEqualNP.Outside module name")
    args = p.parse_args()
    bypass = archived_source(args.archive_or_directory, "RungBypassCritical.lean")
    special = archived_source(args.archive_or_directory, "SpecialPins.lean")
    prefix = initial_part(bypass, "theorem smaller_of_equal").replace(
        "namespace RungEdgeBypass", "namespace PetersenPositivePartner", 1)
    if "theorem byp_ao2" not in prefix and "lemma byp_ao2" not in prefix:
        raise ValueError("Incorrect bypass source, missing byp_ao2")
    pins_prefix = block(special, "namespace PetersenSpecialPins", "theorem agreedFold")
    pins_prefix += block(special, "theorem earlier", "theorem internalPartner")
    part = lambda name: (PARTS / name).read_text(encoding="utf-8")
    singleton = part("singleton.lean.part")
    singleton = singleton.replace(
        "maskedPrefix D same force pre [] (by simp [D])",
        "maskedAll D same force")
    exact = part("bridge.lean.part").replace("theorem PetersenPositivePartner.provedChild :",
                                            "theorem " + args.theorem_name + " :", 1)
    text = "\n".join([prefix, part("positive.lean.part"), pins_prefix,
                      part("masked.lean.part"), singleton, exact])
    args.output.write_text(text, encoding="utf-8")

if __name__ == "__main__":
    main()
