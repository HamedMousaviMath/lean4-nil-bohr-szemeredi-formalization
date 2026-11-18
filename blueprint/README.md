# Blueprints

`compact.tex` is the primary reading guide. `full.tex` develops the estimates and proofs in dependency order. Both use the numbering of the [final manuscript](../paper/current.pdf) and share the catalogue of checked steps. The PDFs are `compact.pdf` and `full.pdf`.

Build both in this directory with a standard TeX Live installation containing the AMS packages, `geometry`, `hyperref`, `booktabs`, `longtable`, and TikZ.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error compact.tex full.tex
```

The source uses standard leanblueprint declaration and dependency tags. Install Graphviz and its development headers, then run these commands from the repository root to rebuild both PDFs and both interactive graphs.

```sh
python3 -m pip install -r blueprint/requirements.txt
bash scripts/render_blueprints.sh
python3 -m http.server --directory blueprint/web 8000
```

Compiled compact and full HTML are supplied in `web/`. Open `http://localhost:8000/compact/` or `http://localhost:8000/full/`. The rebuild writes its output to `build/`. Browser rendering uses MathJax.

From the repository root, run `lake env lean scripts/CheckBlueprint.lean` after building the Lean project to resolve all tagged declaration names. The PDF and web build logs are in [the verification evidence](../evidence/README.md).

Lean declaration names are fully qualified. An open statement can have a Lean target declaration without a proof check mark. Checked conditional deductions state their premises in the text. See the [paper map](../docs/PAPER_MAP.md) and [assumption catalogue](../docs/ASSUMPTIONS.md).
