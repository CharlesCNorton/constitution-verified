"""Check CLAUSES.tsv against the Coq development.

Every clause identifier in the manifest must be defined in theories/ as a
predicate on World, and must appear in the conjunction Constitutional.  Every
clause predicate defined in theories/ must appear in the manifest.  The exit
status is nonzero on any mismatch.

Run from the repository root:
    python tools/check_clauses.py
"""

import csv
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "CLAUSES.tsv"
THEORIES = ROOT / "theories"

CLAUSE_DEF = re.compile(
    r"^Definition\s+(\w+)\s+\(w\s*:\s*World\)\s*:\s*Prop", re.MULTILINE
)


def manifest_ids():
    with MANIFEST.open(encoding="utf-8", newline="") as handle:
        return [row["id"] for row in csv.DictReader(handle, delimiter="\t")]


def defined_clauses():
    found = {}
    for path in sorted(THEORIES.glob("*.v")):
        text = path.read_text(encoding="utf-8")
        for name in CLAUSE_DEF.findall(text):
            found.setdefault(name, path.name)
    found.pop("Constitutional", None)
    return found


def conjoined_clauses():
    text = (THEORIES / "Constitutional.v").read_text(encoding="utf-8")
    body = text.split("Definition Constitutional", 1)[1]
    return set(re.findall(r"\b(\w+)\s+w\b", body))


def main() -> int:
    ids = manifest_ids()
    defined = defined_clauses()
    conjoined = conjoined_clauses()

    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    undefined = [i for i in ids if i not in defined]
    unconjoined = [i for i in ids if i not in conjoined]
    unlisted = sorted(n for n in defined if n not in set(ids))

    print(f"manifest clauses:        {len(ids)}")
    print(f"clause predicates:       {len(defined)}")
    print(f"conjoined in Constitution: {len(conjoined & set(ids))}")
    for label, items in (
        ("duplicate identifiers", duplicates),
        ("manifest ids without a predicate", undefined),
        ("manifest ids missing from Constitutional", unconjoined),
        ("predicates missing from the manifest", unlisted),
    ):
        if items:
            print(f"{label}: {', '.join(items)}")

    mismatches = duplicates + undefined + unconjoined + unlisted
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
