# Verification evidence

## Final manuscript release

- `final-release-summary.txt` records the completed checks. `final-release-lean-replay.log` records the cached build replay and production source screen. The `final-release-lean-*.log` files have the rerun aggregate axiom audit and headline, blueprint, and catalogue declaration checks.
- `final-release-manuscript-latex.log`, `final-release-manuscript-labels.log`, and `final-release-pdf-comparison.log` record the independent compilation, equation-number changes and comparison with the supplied 39-page PDF.
- `final-release-blueprints.log` and `final-release-blueprint-graphs.log` record the two final PDF and HTML builds and graph checks. `final-release-verify.log` records the release verifier, including the final pair's hashes, compiled labels and replay of the manuscript revision patch.

## Interim repository package

- `repository-source-identity.log` and `repository-lean-source-hashes.json` tie the packaged Lean sources and version files byte for byte to the prior manuscript-review build. The revision required documentation and packaging updates, so the clean-build evidence below applies to identical production sources.
- `repository-manuscript-labels.log`, `repository-current-latex.log`, and `repository-corrected-latex.log` record the three-way numbering check and compilation of both manuscript copies.
- `repository-headlines.log` records the headline types and axiom checks. `repository-catalogues.log` records elaboration of every Lean name in the two JSON ledgers. The individual ledger checks are in `repository-assumption-declarations.log` and `repository-paper-map-declarations.log`.
- `repository-blueprint-build.log` and `repository-blueprint-graphs.log` record the rebuilt PDFs, HTML, and graph checks. `repository-release-verify.log` records the package verifier. The GitHub workflow syntax was validated locally. A hosted run requires a GitHub checkout.

## Manuscript-review snapshot

- `manuscript-review-clean-project.log` records the build from an empty project build directory, reusing the pinned dependency artifacts. The log ends with a check of the complete project and a byte-for-byte comparison with the packaged Lean sources. `manuscript-review-summary.txt` records the commands, versions and counts.
- `manuscript-review-axiom-audit.log` records the production source screen and the dependency audit for every public theorem. `manuscript-review-incremental.log` records the integrated build. `manuscript-review-dependency-revisions.log` verifies the checkouts against the manifest.
- `manuscript-review-project-axioms.log` records a second audit from the freshly compiled project. It traverses the dependencies of safe project declarations, including private lemmas and generated equations, using Lean's kernel declaration information.
- `manuscript-review-blueprints-latex.log`, both `manuscript-review-*-web.log` files and `manuscript-review-blueprint-dag.log` record the PDF builds, the PlasTeX builds and dependency graph validation. `manuscript-review-lean-declarations.log` checks the tagged Lean names.
- `manuscript-review-source-integrity.log` verifies the supplied `.tex` and `.pdf` hashes and checks both files against the prior archive.

## Prime distribution snapshot

- `prime-distribution-clean-project.log` records project compilation from an empty project build directory, with the pinned dependency artifacts reused. An initial two-job build of the frozen source set precedes a final `lake build` in the same directory for the integrated project. It checks source identity against the packaged sources. `prime-distribution-summary.txt` gives the compiler, audit and blueprint results.
- `prime-distribution-axiom-audit.log` records `LEAN_NUM_THREADS=1 bash scripts/verify.sh --audit-only` after `lake build` on the identical source tree. It includes the source screen, public theorem dependencies and manuscript hashes. The incremental build output is in `prime-distribution-incremental.log`. The dependency pins are checked in `prime-distribution-dependency-revisions.log`.
- `prime-distribution-blueprints-latex.log`, the two `prime-distribution-*-web.log` files and `prime-distribution-blueprint-dag.log` record the two LaTeX builds, website builds and graph validation. `prime-distribution-lean-declarations.log` records elaboration of the tagged Lean names.
- `prime-distribution-source-integrity.log` checks the manuscript hashes and byte identity with the prior release. `prime-distribution-exact-fourier.log` records the finite diagnostic for the rational coprime Fourier formula. For each listed modulus and numerator, the program cleared the totient denominators and checked an integer polynomial remainder modulo the cyclotomic polynomial. The general formula has a checked Lean proof.

## Foundations snapshot

- `foundations-clean-project.log` records the fresh compilation in a separate project build directory. `scripts/build_two_jobs.py` built the first frozen source set. A final `lake build` in that same directory compiled the four late modules and the complete umbrella. The project compilation reused pinned dependency artifacts. `foundations-summary.txt` records the source comparison and counts.
- `foundations-axiom-audit.log` records `LEAN_NUM_THREADS=1 bash scripts/verify.sh --audit-only` after `lake build` on the identical project sources. It includes the placeholder screen, all public theorem dependencies and manuscript hashes. `foundations-incremental.log` records that compilation. `foundations-dependency-revisions.log` records the checkout revisions verified against the manifest.
- `foundations-blueprints-latex.log` and `foundations-compact-web.log` / `foundations-full-web.log` record the PDF and HTML builds. `foundations-blueprint-dag.log` records graph validation. `foundations-lean-declarations.log` records elaboration of the blueprint declaration names.
- `foundations-source-integrity.log` verifies both manuscript hashes and byte-for-byte agreement with the previous archive. `foundations-exact-selector.log` records the exact rational diagnostic rerun. The diagnostic does not replace the Lean proofs.

## Earlier snapshot

- `verification.log` records `LEAN_NUM_THREADS=2 bash scripts/verify.sh --two-jobs` for the prior snapshot. The command removed the project build outputs, recompiled the project, screened its production sources, audited its public theorems and verified the archived manuscript hashes.
- `audit-summary.txt` gives the theorem count and the union of kernel axiom dependencies. `docs/ASSUMPTIONS.md` records the mathematical premises those proofs use.
- `final-milestone-targets.log` and `green-tao-adapter-target-build.log` record targeted builds of the final additions before the clean run. `green-tao-metric-target-audit.log`, `ambient-sharp-target-audit.log` and `remark-target-audit.log` are earlier focused axiom checks.
- `final-blueprints-latex.log` and `final-blueprint-compact-web.log` / `final-blueprint-full-web.log` record the TeX and PlasTeX runs. `final-blueprint-dag.log` and `final-blueprint-dag-reproduction.log` check the dependency graphs. `final-blueprint-lean-declarations.log` records elaboration of the current tagged Lean declarations.
- `exact-selector-checks.log` and `manuscript-recompile.log` record the earlier exact rational diagnostics and separate recompilation of the preserved manuscript. Older build logs and blueprint sources remain in `docs/history/`.
