# Development log

## 18 November 2026 | Source review and foundations

- Read the active LaTeX and checked the accompanying 38-page PDF. Recorded the numbered statements, proof dependencies and source repairs in `INITIAL_REVIEW.md`. Preserved the source bytes before drafting Lean.
- Inspected Lean and Mathlib. Installed the project-local Lean 4.19.0 binary and pinned Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The cache server rate-limited some initial bulk requests. Repeated cache requests used previously downloaded artifacts and eventually unpacked all 6,641 files.
- Proved the affine rescaling, signed floor and Heisenberg chart identities, finite Diophantine inequalities, the short-interval Gowers cube identity, finite density bookkeeping, complex-weight sieve error estimate and close-spaced subsequence convergence. Proved the ordinary Bohr restriction corollary from KMTT Theorem 1.2 given as an explicit proposition.
- Exact integer and rational diagnostics probed floor and cube boundaries. The attached mathematical review and the diagnostic output are historical notes.

## 18 November 2026 | Discrete and arithmetic comparisons

- Checked the two-input Fourier formula and Plancherel. Established the spatial Cauchy–Schwarz identity, the localized phase product as an ordinary polynomial test, and the horizontal Diophantine bound with the manuscript's exponents and denominator cut.
- Checked squarefree-sieve midpoint domination for complex weights, the exact affine divisor count, and exceptional-divisor summation. Recorded the Green–Tao scalar obstruction and proved the conditional logarithmic saving, with its quotient, filtration and Haar bridge open.
- Checked the density iteration through its exact constants, progression lengths and smoothness budget. Verified the count discrepancy to denser atom, the exact collision bound and higher-prime-power error. Checked Corollary 1.3 from Theorem 1.2 with the sorted enlarged polynomial family.
- Checked the dense admissible Liouville family using Bertrand and upward rounding. Saved the comparison snapshot with the authoritative manuscript and both blueprints.

## 18 November 2026 | Ergodic deductions and verification

- Checked orbit averaging and complex $L^1$ duality, the fixed-family discrete-to-ergodic bound, all-scale convergence from logarithmic decay, and the prime conversion with its actual endpoint correction. The zero-frequency and scalar/weighted interval approximation steps were checked on one conull set for a countable family.
- Checked circle-product rotations, Fubini and the first quadratic-twist deductions in Corollary 1.5. The discontinuous horizontal factors in the bracket phase remain an analytic obligation.
- A first clean command also removed dependency build outputs. Interrupted that build, restored the cached artifacts from local archives, and changed verification to clear the project build directory only. The successful final run is recorded with its actual commands.

## 18 November 2026 | Conditional analytic and recurrence proofs

- Derived the weighted local inverse lemma from KMTT's unweighted theorem. Checked finite Plancherel on the common spatial progressions, the simultaneous dual replacement, and the local block deletion argument. Assembled the full longer-family Theorem 4.2. The weighted inverse interface's modulus exponent is chosen after fixing $C,d,k$.
- Assembled the smooth-modulus prime estimate using Banks's zero exclusion and the ambient, dilation and relative Cramér inputs. Checked the Fourier multiplier, quantitative interior cutoff partition, horizontal-circle projection, and the two count discrepancies. This gives the uniform relative selector comparison and the main recurrence deductions.
- Checked the product obstruction argument, including signed binomial rounding, periodic integer phases on the cover and short-prefix loss. Proved the centered estimate (24) using the seam cutoff and the full Lipschitz vertical test, then discharged the original phase obligation in the recurrence chain. Checked the ergodic comparison with its uniform $L^1$ constant and the bracket discontinuity passage downstream of Proposition 6.2.
- Checked the reduced-residue prime progression, the exact divisor lengths and logarithmic scaling, and the application of the twisted estimate to good divisors. Proved the localized prime-model inequality by finite Fourier expansion with an interval coefficient sum bounded by $2+\log X$ and the model’s exact Euler normalization.
- Updated both blueprints and preserved the previous sources and PDFs in `docs/history/blueprint-before-continuation.tar.gz`. Proposition 6.2, the adapters to Green–Tao and Appendix A remain separate proof obligations in the map.

## 18 November 2026 | Prime-weighted phase and pointwise results

- Restored the saved source checkpoint and the pinned Lean toolchain. Several Mathlib cache downloads returned HTTP 429. Reused downloaded archives and capped the downloader's parallel requests. The cache eventually unpacked all 6,641 archives. A wide initial build stalled under I/O pressure and was interrupted. Successful target builds and the clean, two-job rebuild are recorded separately.
- Specified the dimension-one fundamental sieve lemma and the Mertens interval consequence using Koukoulopoulos. Proved the uniform sieve specialization at the required floored level, handling an empty retained prime set directly, and checked the finite affine normalization and harmonic error absorption.
- Proved the prime-weighted seam estimate, then passed the finite model discrepancy through the absolutely summable vertical Fourier series. Sifted the full centered chart test and combined all three contributions at the original shifted-prime scale. The new proofs of Proposition 6.2, Proposition 7.1, Theorem 1.4 and Corollary 1.5 take only named literature and specialized Green–Tao interfaces.
- Checked the concrete filtered polynomial orbits and the normalized left-invariant Heisenberg chart functional. Verified Appendix A's phase and count dilation identities, Fourier extraction on the denominator multiples and the explicit quadratic approximation. The remaining Green–Tao adapters and Appendix A limit theorem are recorded in the restart document.

## 18 November 2026 | Separating scales and the degree-uniform inverse theorem

- Constructed the exact floored modulus and parameter sequence of Appendix A. The numerical proofs check the smooth-modulus window, logarithmic equivalences, bracketing, coprimality and the two vanishing error ratios for the quadratic argument.
- Proved the lower bound on the global quadratic phase norm using fixed-shift van der Corput and finite Fourier extraction. On the same sequence proved arbitrary logarithmic decay on the tested progressions and nondecay of the full Gowers norm at every fixed order at least three. The Gowers deduction uses the existing scalar chart input and a fixed nonzero cutoff.
- Checked both exact dilation normalizations in their fixed-family estimates, divergence of the resulting bounds at the indicated exponents, and the repeated-input endpoint. The direct local count bound is uniform over the manuscript’s spatial inputs.
- Read KMTT Lemma 3.4 in the cited version and exposed its degree-only modulus exponent choice. Propagated the fixed exponent through the weighted inverse argument to recover the printed quantifier order in Lemma 5.1. The earlier fixed-family interface remains available to the recurrence proof.
- Checked the introductory Bohr eigenfunction example from Vinogradov. The proof uses the exact open symmetric arc, computes its first Fourier integral and normalizes by the selected prime density.
- Checked the introductory irrational-parameter counterexample. Euclid and upward rounding produce exact one-sided exponential approximation, and the two actual phase coefficients give an exact grid partition of the denominator multiples. A largest cell avoids the arc for every shift. The scale and cardinality estimates show that the same sequence of cells eventually exceeds each fixed positive polylogarithmic density threshold.
- Certified the analytic Heisenberg Lie group and the compact Hausdorff coset quotient. Promoted the chart functional to an invariant Borel probability using the cube pushforward and Fubini. Checked the two product chain projection bounds, periodicity and the induced Lipschitz bound of the product test. The chain metric topology and further certificates for the quantitative Leibman application remain open.


## 18 November 2026 | General Green–Tao transfer and introductory deductions

- Expressed the one-parameter quantitative Leibman theorem with constants uniform in dimension and filtration degree, the actual right-coset metric, complex test bounds, and differences at zero for the circle-valued coefficients. Verified Green–Tao’s Definitions 1.1, 1.2, 2.1–2.7 and 6.1, and Theorem 2.9 in the Annals paper.
- Checked the scalar and product canonical manifold Lie brackets, the adapted ordered one-parameter axes, and the lattice and rational height bounds. Checked the group and quotient chain metrics and compatibility with ordinary topologies. Constructed both Haar probabilities from unit-mass fundamental domains, verified chart integration and proved uniqueness. Applied the general theorem to both models with the correct product tolerance, then recovered the specialized character and binomial bounds.
- Completed the alternate local-factor proof in Remark 1.6. Absorbed the auxiliary denominator into the next fixed power through the least-common-multiple hypothesis of the density increment. Made the derivative frequency zero in the global extraction and kept the ordinary local testing on each cell. Preserved the previous local theorem and the full range of the main comparison.
- Checked the rotation extension, the finite Fourier congruence inversion, continuous torus weights, simultaneous interval cutoffs and their stated normalizations. Applied the relative-density and quantitative Green–Tao bounds to fixed and moving windows. Recorded the distinct length-four threshold and the classical fixed-modulus prime-count input.
- Checked the square-root-scale ambient sharp selector comparison uniformly over the spatial set, the $q=1$ norm obstruction and the irrational quadratic $U^2$ counterexample. Verified the initial-cutoff and empty-set cases of maximal domination and the elementary introductory recurrence and coloring examples. The manuscript copies were preserved throughout.

## 18 November 2026 | Finite foundations and final scope review

- Checked multilinear Gowers–Cauchy–Schwarz, the triangle law, adjacent-order comparison, the progression phase-norm bound and normalized dilation. The reindexing handles all surviving cube directions. The ambient dilation endpoint uses the all-zero-direction bound for a singleton. The residue restriction has Fourier mass one.
- Proved the Lipschitz circle Fourier bound by difference quotients and Parseval. Assembled the manuscript’s localized multiplier without analytic inputs. The new recurrence and pointwise wrappers supply the proved norm estimates and use the general quantitative Leibman premise directly.
- Derived the exact weak-regularity interface used by the density increment from KMTT’s local inverse input. The proof gives the fixed progression factors, reanchors the count for a base-coordinate residual and uses zero atom means to contradict the inverse correlation.
- Checked the ordinary, theta and psi PNT conversions and the fixed-modulus logarithmic integral normalization. Derived the qualitative prime progression interface used by the fixed-window implication from the quantitative bound used by the shrinking-window implication.
- Filled in the end of Appendix A on the sizes of the iteration moduli, including uniformity over stages and the large admissible witness at polylogarithmic density. Checked the open Heisenberg window, exact Haar mass and return equivalence under the positive-time convention. Recorded the optional time-zero clarification without altering the submission.
- Archived the earlier blueprint sources and PDFs in `docs/history/blueprint-before-foundations.tar.gz`. Both new PDFs compile, and their HTML graph references and Lean declaration names resolve. The evidence index identifies the full project build and audit.

## 18 November 2026 | Removing independent prime distribution premises

- Averaged the sieve bounds over a complete period to recover the exact totient density. On the actual interval and on a reduced progression, counted the occurrences of each divisor with discrepancy at most one. Checked ordinary PNT and fixed-modulus PNT from Banks, KMTT's ambient model, Mertens and the fundamental sieve lemma.
- Proved irrational linear cancellation for the Cramér model by reduced Dirichlet approximation and a complex sieve midpoint. The rational coefficient comes from finite Möbius inversion and has norm at most $\sqrt{2/q}$. The growing denominators require only irrationality at each large cutoff, and the sieve level and Euler normalization errors vanish at those same cutoffs.
- Transferred the linear estimates through the ambient $U^2$ bound, removed higher prime powers and logarithmic weights, and passed to all continuous circle tests. The Heisenberg and bracket pointwise wrappers now share the same independent premises. Retained the previous exact-input interfaces for other uses.
- Preserved the earlier blueprints in `docs/history/blueprint-before-prime-distribution.tar.gz` and checked both current blueprints. The supplied LaTeX and PDF match the prior foundations release byte for byte.

## 18 November 2026 | Manuscript coverage audit

- Compared the manuscript's numbered results and substantial supporting claims with the actual Lean declarations. The earlier Proposition 7.1 wrapper required an ordered family. A checked degree permutation now gives the original unordered formulation, with the same orbit products, essential sup norms and uniform quantifiers. The combined Proposition 4.3 statement shares the denominator sequence across all three estimates, and Lemma 6.1 now exposes its lower constant before the choice of $\beta$.
- Checked three introductory statements in their explicit forms. The complexified distance to the window's complement realizes the nil-Bohr selector. The localized correlation and $U^3$ estimate allow every prescribed mode and cutoff in the printed range. Taking suprema and then $L^p$ norms verifies the conditional maximal transfer and its independence of a.e. representatives.
- Checked the exact log-lcm identity and the initial and stage modulus bounds using Chebyshev's estimate. Proved the quantitative Fourier tail and uniform truncation limit used in Proposition 6.2. Verified the Appendix's logarithmic ratios, divisibility, growing-shift estimate and subpower coefficient limit. The earlier alternate proofs of the conclusions remain available.
- Updated both blueprints and the statement map. The previous blueprint source and PDFs are retained in `docs/history/blueprint-before-manuscript-review.tar.gz`. The manuscript bytes and the independent literature premises are recorded in the verification and assumption files.
- Rebuilt the complete project from an empty project build directory using the pinned dependency artifacts. Checked both PDFs and their dependency graphs, and audited all safe project declarations in the freshly compiled environment.

## 18 November 2026 | Revised manuscript and repository package

- Compared the latest supplied LaTeX with the earlier manuscript. The new Section 5 display after the last input replacement already follows from the checked common-modulus replacement theorem. All 87 active labels kept their numbers.
- Preserved the new upload byte for byte and compiled it. Listed the exact remaining replacements and compiled a separate copy incorporating them. The original source/PDF pair stays in the manuscript archive.
- Prepared the repository with citation metadata, exact statement and external-input ledgers, headline checks, interactive blueprints and a CI workflow. All production Lean sources match the clean build of the manuscript-review snapshot. Rechecked the headline types and axioms, all ledger declarations, and the blueprint declarations.

## 18 November 2026 | Final supplied manuscript

- Preserved the final supplied LaTeX and PDF and checked their correspondence against an independent compilation. The new equation (44) labels a checked prefix bound on the cover. The 19 numbered mathematical items retain their numbers.
- Recorded the author-adopted proof changes in the manuscript report and updated the statement map, compact blueprint and expository blueprint to the final equation numbering.
- Replayed the checked Lean build after confirming production-source and pin identity. Reran the aggregate axiom audit and the headline, blueprint and catalogue declaration checks, verified the final manuscript revision patch and regenerated the package checksums.
