# Quantitative polynomial Szemerédi theorems along shifted primes with nil-Bohr restrictions

This Lean 4 project gives a checked conditional formalization of the final supplied manuscript. Start with the [compact blueprint](blueprint/compact.pdf), [statement map](docs/PAPER_MAP.md), and [assumption catalogue](docs/ASSUMPTIONS.md). The [expository blueprint](blueprint/full.pdf) gives the mathematical arguments in detail. The final supplied [LaTeX](paper/current.tex) and [PDF](paper/current.pdf) are the reference pair for this release.

## External theorems assumed in Lean

The numbered results use 11 independent literature inputs. The introductory application to progressions inside the selected primes uses a twelfth, Teräväinen–Wang's theorem. The interfaces below enter as explicit hypotheses in Lean, and Lean checks the deductions from them. The catalogue gives the precise statements, quantifiers, normalizations, and any specialization from the cited source. [Assumption catalogue](docs/ASSUMPTIONS.md) · [Machine-readable input ledger](docs/EXTERNAL_INPUTS.json)

KMTT denotes Krause, Mousavi, Tao and Teräväinen, *Quantitative bounds for sets lacking polynomial progressions with shifted prime difference*.

| External result | Lean hypothesis | Source |
| --- | --- | --- |
| Shifted-prime polynomial recurrence for distinct degrees | [`KMTTShiftedPrimeDensityBound`](NilBohr/Bohr.lean) | [KMTT, Theorem 1.2](https://arxiv.org/html/2608.19525v1) |
| Coefficient-uniform inverse theorem for the unweighted polynomial count | [`KMTTLocalInverseDegreeUniform` and `KMTTLocalInverse`](NilBohr/External.lean) | [KMTT, Lemma 3.4](https://arxiv.org/html/2608.19525v1#S3.Thmtheorem4) |
| Weighted generalized von Neumann bound in terms of the Gowers norms, with independent spatial and parameter lengths | [`KMTTWeightedGowers`](NilBohr/External.lean) | [KMTT, Proposition 3.3](https://arxiv.org/html/2608.19525v1) |
| Effective bound on real zeros of primitive real Dirichlet characters | [`BanksRealZeroBound`](NilBohr/External.lean) | [Banks, Theorem 1.1](https://arxiv.org/html/2610.15483v1) |
| Ambient Gowers approximation of the von Mangoldt function by the Siegel model | [`KMTTAmbientPrimeModel`](NilBohr/GowersComparison.lean) | [KMTT, Lemma 3.1, equation (3.1)](https://arxiv.org/html/2608.19525v1) |
| Relative Cramér-model Gowers estimate at smooth moduli | [`KMTTRelativeCramer`](NilBohr/GowersComparison.lean) | [KMTT, Lemma 4.3(i), equation (4.28)](https://arxiv.org/html/2608.19525v1) |
| One-parameter quantitative Leibman theorem for polynomial nilmanifold orbits | [`GreenTaoQuantitativeLeibman`](NilBohr/GreenTaoLiterature.lean) | [Green–Tao, Theorem 2.9](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf) |
| Uniform interval product bound from Mertens' product theorem | [`MertensIntervalProductBound`](NilBohr/SieveLiterature.lean) | [Koukoulopoulos, Theorem 3.4(c)](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) |
| Fundamental lemma of the sieve in dimension one | [`FundamentalSieveLemma`](NilBohr/SieveLiterature.lean) | [Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) |
| Fixed-family count bound in terms of ordinary polynomial-phase correlations | [`TeravainenFixedFamily`](NilBohr/External.lean) | [Teräväinen, Theorem 4.1, equation (4.1)](https://arxiv.org/html/2401.03174v2) |
| Almost-everywhere convergence of the unrestricted Mangoldt-weighted polynomial averages for distinct degrees | [`MirekWanWrightPointwise`](NilBohr/ErgodicLimits.lean) | [Mirek–Wan–Wright, Theorem 1.1(ii), v2](https://arxiv.org/pdf/2505.15549v2) |
| Progression bounds in sparse subsets of the primes, used in the introduction | [`TeravainenWangSparseGreenTao`](NilBohr/BohrPrimeProgressions.lean) | [Teräväinen–Wang, Theorem 1.1](https://arxiv.org/html/2603.09281v1) |

| Manuscript result | External inputs used by its Lean proof |
| --- | --- |
| Corollary 1.1, Bohr-restricted recurrence | KMTT's shifted-prime recurrence theorem. |
| Theorem 1.2 and Corollary 1.3, nil-Bohr and bracket recurrence | Banks's zero bound, KMTT's ambient and relative prime models, KMTT's inverse theorem and weighted Gowers bound, and Green–Tao's quantitative Leibman theorem. |
| Theorem 4.2, coefficient-uniform local generalized von Neumann bound | KMTT's unweighted inverse theorem. Lean proves the two-input case under the manuscript hypotheses alone. |
| Proposition 6.2, centered prime-weighted phase estimate | Banks's zero bound, KMTT's ambient prime model, Mertens' interval product bound, the fundamental sieve lemma, and Green–Tao's quantitative Leibman theorem. |
| Theorem 1.4 and Corollary 1.5, pointwise convergence | The five inputs for Proposition 6.2, Teräväinen's fixed-family count bound, and Mirek–Wan–Wright's pointwise theorem. |
| Proposition A.1, separating family | Green–Tao's quantitative Leibman theorem. The subsequent count comparison also uses KMTT's inverse theorem and Teräväinen's fixed-family estimate. |

Lean derives the weak regularity used in the density increment from KMTT's inverse theorem. It derives the ordinary and fixed-modulus prime number theorems and irrational linear equidistribution along the primes from Banks's zero bound, KMTT's ambient prime model, Mertens' bound, and the fundamental sieve lemma. The introductory maximal domination transfers an assumed unrestricted maximal estimate to the selected averages. [Detailed proof boundary](docs/ASSUMPTIONS.md#boundaries-of-the-checked-deductions)

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
