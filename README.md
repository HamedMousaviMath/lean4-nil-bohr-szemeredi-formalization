# Quantitative polynomial Szemerédi theorems along shifted primes with nil-Bohr restrictions

This Lean 4 project gives a checked conditional formalization of the final supplied manuscript. Start with the [compact blueprint](blueprint/compact.pdf), [statement map](docs/PAPER_MAP.md), and [assumption catalogue](docs/ASSUMPTIONS.md). The [expository blueprint](blueprint/full.pdf) gives the mathematical arguments in detail. The final supplied [LaTeX](paper/current.tex) and [PDF](paper/current.pdf) are the reference pair for this release.

## Verified scope

- Corollary 1.1 follows from KMTT Theorem 1.2. Lemma 6.1, the dense admissible Liouville construction and the two-input case of Theorem 4.2 have checked proofs under the manuscript's hypotheses.
- The full Theorem 4.2 follows from KMTT's unweighted inverse theorem. The longer-family argument includes weighted inverse extraction, dual replacements, deletion of block boundaries and a genuine local ordinary-phase test. Lemma 5.1 also checks with the modulus exponent chosen from the degree alone, as in the manuscript.
- Proposition 4.1 uses the quoted prime-model bounds and zero exclusion. The interval and progression Gowers laws, normalized dilation and Lipschitz Fourier summability all have checked proofs. Lemma 4.5 then checks under its own hypotheses. The scalar, twisted and cutoff-free centered estimates in Proposition 4.3 follow from Green–Tao quantitative Leibman through the checked scalar and product adapters.
- Theorem 3.2, Proposition 3.1, Theorem 1.2 and Corollary 1.3 have checked proofs from the listed external inputs. The recurrence proof includes the centered estimate (27) and obtains weak regularity from the same inverse theorem used in Theorem 4.2.
- Proposition 6.2, Proposition 7.1, Theorem 1.4 and Corollary 1.5 also have checked proofs from explicit literature inputs and the same specialized Green–Tao obstructions. The ambient model and sieve premises already used in Proposition 6.2 supply ordinary and fixed-modulus PNT and irrational linear prime equidistribution. The two pointwise theorem wrappers therefore take the same independent premises.
- Appendix A.1 checks on the paper’s separating sequence. The global $u^3$ and Gowers lower bounds, local logarithmic upper bound and direct count bound use the same scales. The fixed-shift comparison checks both normalization losses and the repeated-input endpoint $K=1$. The final scale comparison gives uniform small moduli at double-logarithmic density and constructs large admissible moduli at the polylogarithmic threshold.
- The introductory obstruction under irrationality alone checks under the paper's hypotheses. One irrational $\beta$ with sufficiently fast prime-denominator approximants gives, for every $\alpha$, a sequence of sets that avoids the stated nil-Bohr arc and eventually exceeds each fixed positive polylogarithmic density threshold.
- For Remark 1.6, the alternate local-factor proof uses the density-increment hypothesis $\mathcal L(w)\mid q$. It selects the zero derivative frequency on fixed-power spatial progressions, with the final bound uniform over the coefficient class.
- The introductory extensions check the open Heisenberg window and its Haar mass, fixed congruence restrictions, continuous and simultaneous interval Bohr weights, both prime progression implications, and restricted maximal domination. The ambient sharp-arc comparison and the $q=1$ Gowers and $U^2$ examples also check. The introductory Bohr eigenfunction example uses the derived scalar equidistribution interface.
- The Green–Tao applications use the actual manifold Lie groups and adapted rational bases, exact chain metrics, and unique normalized Haar quotient probabilities. The [statement map](docs/PAPER_MAP.md) and [assumption catalogue](docs/ASSUMPTIONS.md) record the corresponding declarations and all literature premises.
- The manuscript coverage audit checked Proposition 7.1 for distinct degrees in arbitrary order. It also checked the continuous nilsequence realizing the return window, the prescribed-cutoff $U^3$ bound, the conditional maximal $L^p$ estimate, the linear initial and stage modulus bounds, Proposition 6.2's quantitative Fourier truncation, and the Appendix's exact scale limits and growing-shift bound.

## Build and audit

Install [Elan](https://github.com/leanprover/elan), then run these commands in the repository directory.

```sh
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckProjectAxioms.lean
lake env lean scripts/CheckHeadlines.lean
lake env lean scripts/CheckBlueprint.lean
lake env lean scripts/CheckCatalogues.lean
python3 scripts/verify_release.py
sha256sum -c SHA256SUMS.txt
```

Lean 4.19.0 and the Mathlib revision are pinned in `lean-toolchain` and `lakefile.toml`. Transitive dependency revisions are in `lake-manifest.json`. With Bash, Git, Python 3 and ripgrep available, `scripts/verify.sh` checks source placeholders, removes the project's build outputs and reruns the build, axiom audit and manuscript checksum verification. Dependency artifacts can be reused. Run `scripts/verify.sh --two-jobs` to limit concurrent project compilation to two ready modules. The actual compiler and audit logs are in [evidence](evidence/).

The [machine-readable assumption ledger](docs/EXTERNAL_INPUTS.json) records the independent inputs, exact Lean declarations, and derived interfaces. The [module index](docs/MODULE_INDEX.md) organizes the implementation by subject. The [GitHub Actions workflow](.github/workflows/ci.yml) runs verification on a fresh checkout.

[Blueprint build instructions](blueprint/README.md) cover the LaTeX, PDF and HTML versions. The [final manuscript report](docs/CORRECTIONS.md) records the adopted fixes and the equation-number changes. The initial supplied pair is preserved in [manuscript](manuscript/), and the interim review files are in [paper/history/review](paper/history/review/). Run `python3 scripts/exact_selector_checks.py` to reproduce the finite exact rational diagnostics.

See [RESTART.md](RESTART.md) for the current proof boundary and next obligations.
