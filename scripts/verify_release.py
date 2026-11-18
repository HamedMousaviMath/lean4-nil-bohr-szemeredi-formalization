#!/usr/bin/env python3
"""Verify provenance and declaration catalogues for this release."""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
LABEL = re.compile(r"\\label\{([^{}]+)\}")
BEGIN = r"\\begin\{(theorem|proposition|lemma|corollary|remark|definition)\}"
AUX_LABEL = re.compile(r"^\\newlabel\{([^{}]+)\}\{\{([^{}]*)\}", re.MULTILINE)
PROOF_PINS = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}


def read(path):
    return (ROOT / path).read_text()


def digest(path):
    return sha256((ROOT / path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def json_file(path):
    return json.loads(read(path))


def check_proof_snapshot():
    hashes = json_file("evidence/repository-lean-source-hashes.json")
    lean_files = {"NilBohr.lean"} | {
        file.relative_to(ROOT).as_posix() for file in (ROOT / "NilBohr").glob("*.lean")
    }
    require(set(hashes) == lean_files | PROOF_PINS, "Lean source manifest file set differs")
    for path, expected_hash in hashes.items():
        require(digest(path) == expected_hash, f"Lean snapshot differs for {path}")
    print(f"Checked source identities for {len(lean_files)} Lean modules and {len(PROOF_PINS)} version files.")


def check_paper(aux_path):
    ledger = json_file("docs/PAPER_MAP.json")
    source_path = ledger["manuscript"]["path"]
    source_hash = digest(source_path)
    require(source_hash == ledger["manuscript"]["sha256"], "Final manuscript source hash differs")
    label_ledger = json_file("paper/labels.json")
    require(source_hash == label_ledger["tex_sha256"], "Final label ledger source hash differs")
    require(digest("paper/current.pdf") == label_ledger["pdf_sha256"], "Supplied final PDF hash differs")
    labels = label_ledger["labels"]
    if aux_path:
        actual = {name: number for name, number in AUX_LABEL.findall(aux_path.read_text())
                  if not name.startswith("tocindent")}
        require(actual == labels, "Compiled manuscript labels differ from the final label ledger")
    source = read(source_path)
    statements = ledger["statements"]
    scope = ledger["scope"]
    require(len(statements) == scope["numbered_items"], "Wrong ledger statement count")
    require(len(statements) == len({entry["number"] for entry in statements}), "Duplicate statement numbers")
    observed_status = Counter(entry["status"] for entry in statements)
    for key, status in (
        ("formalized_definitions", "formalized_definition"),
        ("proved_under_paper_hypotheses", "proved_under_paper_hypotheses"),
        ("checked_conditional_deductions", "checked_conditional_deduction"),
    ):
        require(observed_status[status] == scope[key], f"Incorrect {key} count")
    lines = source.splitlines()
    targets = set()
    for entry in statements:
        number = entry["number"]
        excerpt = "\n".join(lines[entry["source_start_line"] - 1:entry["source_end_line"]])
        opening = re.match(BEGIN, excerpt)
        require(opening is not None and opening[1] == entry["kind"], f"Wrong source slice for {number}")
        require(LABEL.findall(excerpt)[:1] == ([entry["latex_label"]] if entry["latex_label"] else []),
                f"Wrong source label for {number}")
        if entry["latex_label"]:
            require(labels.get(entry["latex_label"]) == number, f"Wrong printed label number for {number}")
        require(entry["statement_tex"] in excerpt, f"Statement text differs for {number}")
        targets.update(entry["lean_declarations"])
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / "paper").mkdir()
        copy = work / "paper/current.tex"
        copy.write_bytes((ROOT / "paper/history/review/current.tex").read_bytes())
        subprocess.run(["git", "apply", "--no-index", "--whitespace=nowarn",
                        str(ROOT / "paper/manuscript-revisions.patch")], cwd=work, check=True)
        require(copy.read_bytes() == (ROOT / source_path).read_bytes(),
                "Revision patch does not reconstruct the final supplied LaTeX")
    print(f"Checked {len(statements)} numbered items against {len(labels)} final labels.")
    print("Verified the final LaTeX and PDF hashes and replayed the manuscript revision patch.")
    if aux_path:
        print("Compiled manuscript labels match the final label ledger.")
    return targets


def check_external_inputs():
    catalogue = json_file("docs/EXTERNAL_INPUTS.json")
    keys = {entry["id"] for entry in catalogue}
    require(len(keys) == len(catalogue), "Duplicate external input ID")
    names = set()
    for entry in catalogue:
        require(entry["declared_as_Lean_axiom"] is False, f"Unexpected input status for {entry['id']}")
        unknown = set(entry.get("independent_input_ids", [])) - keys
        require(not unknown, f"Unknown dependencies for {entry['id']}: {unknown}")
        for key in ("lean_interfaces", "checked_proofs"):
            for item in entry.get(key, []):
                require((ROOT / item["file"]).is_file(), f"Missing source for {item['declaration']}")
                names.add(item["declaration"])
        names.update(entry.get("consumed_by", []))
    independent = sum(entry["status"] == "consumed_explicit_hypothesis" for entry in catalogue)
    print(f"Checked {len(catalogue)} catalogue entries, including {independent} quoted independent inputs.")
    return names


def check_declarations(catalogue_targets):
    blueprint_targets = set()
    for source in (ROOT / "blueprint").glob("*.tex"):
        for tag in re.findall(r"\\lean\{([^{}]+)\}", source.read_text()):
            blueprint_targets.update(n.strip() for n in tag.split(",") if n.strip().startswith("NilBohr."))

    def checked_names(script):
        return set(re.findall(r"^#check (NilBohr\.\S+)", read(script), re.MULTILINE))

    require(blueprint_targets == checked_names("scripts/CheckBlueprint.lean"), "Blueprint and check targets differ")
    require(blueprint_targets == set(read("lean_decls").splitlines()), "Lean declaration list differs")
    require(catalogue_targets == checked_names("scripts/CheckCatalogues.lean"), "Catalogue and check targets differ")
    print(f"Checked target lists for {len(blueprint_targets)} blueprint tags and {len(catalogue_targets)} catalogue names.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manuscript-aux", type=Path, help="Compare a local manuscript compilation")
    args = parser.parse_args()
    check_proof_snapshot()
    paper_targets = check_paper(args.manuscript_aux)
    external_targets = check_external_inputs()
    check_declarations(paper_targets | external_targets)


if __name__ == "__main__":
    main()
