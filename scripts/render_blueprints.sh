#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../blueprint"

mkdir -p build/print
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/print compact.tex full.tex
plastex -c plastex.cfg -d build/web/compact web.tex
plastex -c plastex.cfg -d build/web/full full-web.tex
python3 ../scripts/check_blueprint_dag.py build/web/compact build/web/full
