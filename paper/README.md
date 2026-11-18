# Manuscript files

| File | Provenance |
| --- | --- |
| `current.tex` | Byte-identical copy of the final supplied LaTeX. |
| `current.pdf` | Byte-identical copy of the supplied 39-page final PDF. |
| `SHA256SUMS` | Checksums for the final pair, verifiable from this directory. |
| `labels.json` | Printed numbers of the 88 active labels in the final source. |
| `manuscript-revisions.patch` | Unified diff from the previous supplied LaTeX to the final LaTeX. |
| [`history/review/`](history/review/) | Previous supplied source, its locally compiled PDF, and the interim proposed corrections. |
| [`../manuscript/`](../manuscript/) | The original supplied LaTeX/PDF pair and its original checksums. |

The bibliography is inline. Run these commands from the repository root with TeX Live and latexmk installed.

```sh
mkdir -p paper/build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=paper/build paper/current.tex
python3 scripts/verify_release.py --manuscript-aux paper/build/current.aux
```

The [statement map](../docs/PAPER_MAP.md) uses the final equation numbering. The [manuscript report](../docs/CORRECTIONS.md) describes the final pair and its correspondence with Lean.
