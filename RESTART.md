# Restart

## Source and verification

`paper/current.tex` and `paper/current.pdf` preserve the final supplied pair. The initial submission is in `manuscript/`, and the interim review files are in `paper/history/review/`. The final manuscript adds equation (44), shifting the subsequent equation numbers by one. The numbered mathematical statements retain their numbers. See `docs/CORRECTIONS.md` and `paper/labels.json`.

Lean 4.19.0 (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. The final release verifies byte identity with the earlier clean build and reruns the project-wide axiom and declaration checks on the matching artifacts. The checks are indexed in `evidence/README.md`.

## Proof boundary

- **Recurrence.** `heisenbergRecurrence_of_analytic_inputs` and `bracketRecurrence_of_analytic_inputs` take the prime model, zero exclusion, inverse, weighted count and quantitative Leibman inputs. `KMTTLocalInverse.toLocalWeakRegularity` supplies the local factors. The normalized dilation, interval and progression Gowers laws and Lipschitz circle Fourier estimate are checked.
- **Pointwise convergence.** `heisenbergPrimeLocalPhase_of_literature` proves Proposition 6.2 from the prime-phase bundle. `heisenberg_pointwise_of_prime_model` and `bracket_pointwise_of_prime_model` use the same seven explicit literature premises. They derive ordinary PNT and irrational linear equidistribution from the existing model and sieve. `primeNumberTheoremInProgressions_of_kmtt_and_sieve` supplies the fixed-modulus reduced-class asymptotic for the congruence extension.
- **Green–Tao geometry.** Both actual Lie brackets, adapted rational bases, chain metrics, quotient topologies, normalized Haar integrals and Haar uniqueness are checked. The adapters verify the rationality parameter, finite interval, test norm, horizontal character and binomial coefficients. Quantitative Leibman remains external. The Heisenberg window's openness, mass and nonzero-time return identity are checked.
- **Appendix and introductions.** `appendixA_separating_family_of_quantitativeLeibman` verifies Proposition A.1. The count comparison, uniform small-modulus statement, fixed-power absorption and admissible large-modulus construction are checked. `centeredSelectorComparison_on_lcm_moduli_of_obstructions` verifies Remark 1.6 at the least-common-multiple moduli used by the density increment. The introductory applications are indexed in the statement map.
- **Manuscript coverage audit.** The exact arbitrary-order form of Proposition 7.1 is in `UnorderedErgodicComparison.lean`. Proposition 4.3 has a combined same-sequence theorem. The audit also supplied the continuous window test, the displayed prescribed-cutoff Gowers bound, the conditional maximal norm, the exact logarithmic lcm identity and Chebyshev bound, the Fourier truncation error, and the Appendix's printed scale and Weyl estimates. The [statement map](docs/PAPER_MAP.md) gives the individual declarations.

## Continuation

The project boundary is the published literature inputs listed in `docs/ASSUMPTIONS.md`. The manuscript's further questions on general nilsequences, variation and other multiplicative weights do not pose formal theorem obligations. For a revised manuscript, compare its numbering and hypotheses with `docs/PAPER_MAP.md` and rerun `bash scripts/verify.sh --two-jobs` plus the blueprint declaration checks before updating the coverage claims. Earlier source snapshots and working notes are retained in `docs/history/` and `docs/DEVELOPMENT_LOG.md`.

To reduce the remaining analytic premises further, the next concrete input is `MertensIntervalProductBound`. A route is to bound Chebyshev's functions using Mathlib's primorial estimate and the existing prime-power bound, prove $\sum_{p\le x}\log p/p=\log x+O(1)$ through the logarithm of a factorial, and apply Abel summation uniformly on $(u,v]$. That argument is outside the checked proof in this snapshot.
