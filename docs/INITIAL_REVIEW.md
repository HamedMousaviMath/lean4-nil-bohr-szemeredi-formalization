# Independent manuscript audit

Source of record: `Pasted text(7).txt`, SHA-256 `129c631521748e35e9d228494e03fad5ec61a10accd02d845eada327a2a1c4db`. The title is *Quantitative polynomial Szemerédi theorems along shifted primes with nil-Bohr restrictions*. The LaTeX sets both author and date to blank. The supplied PDF has 38 pages, with SHA-256 `a71100296a110c97fea239cdd214e509dab15e0150edc10f731e6c6d5b389feb`. The PDF creation metadata reads November 18, 2026. This is not a manuscript version designation. The active label sequence and statements below agree with the supplied PDF. Build artifacts from a future LaTeX compilation may paginate differently.

## Numbered statements and dependencies

| PDF | LaTeX label | Mathematical content and dependencies |
| --- | --- | --- |
| Corollary 1.1 | `c:bohr` | Recurrence with finitely many linear Bohr conditions when a linear shift is present. Finite torus partition and KMTT Theorem 1.2. Independent of the nil-Bohr proof. |
| Theorem 1.2 | `t:recurrence` | For every fixed distinct-positive-degree family with zero constant terms, fixed admissible α and β and fixed proper open arc J, sufficiently dense sets contain pairwise-distinct selected-shifted-prime configurations. Depends on Proposition 3.1 and quantitative density iteration. |
| Corollary 1.3 | `c:bracket-recurrence` | Same recurrence for the bracket phase at p. Depends on Theorem 1.2 for the degree-enlarged family, a finite partition and exact floor analysis. |
| Theorem 1.4 | `t:pointwise` | Normalized selected prime count tends to `|J|` relative to all primes, and the averages converge a.e. to the unrestricted limit. Depends on Proposition 7.1, smooth squeezing, countable intersection, and Mirek–Wan–Wright plus PNT/partial summation for the unrestricted limit. |
| Corollary 1.5 | `c:bracket-pointwise` | Theorem 1.4 for the bracket phase at p. Depends on Theorem 1.4 in product systems for fixed polynomial twists, circle-prime equidistribution, approximation and an exact floor identity. Correct the reindexing error below. |
| Remark 1.6 | none | An alternative centered-selector proof for smooth q using divisibility to absorb inverse denominators. No subsequent numbered proof uses it. Its sketch corresponds to choosing threshold δ = w^{-ε}, with ε small enough that q′ ≪ δ^{-O(1)} ≤ w, so q′ divides q. The phase proof is then simpler on common q-power progressions. |
| Definition 2.1 | `d:Cq` | Coefficient class extends fixed polynomial coefficients to the rescaling P(qy)/q. Positive q and positive polynomial degree matter, and signed leading coefficients are permitted. |
| Proposition 3.1 | `p:selected-density-increment` | Higher density on a long q^B progression with absence of selected configurations preserved by rescaling. Depends on Theorem 3.2, KMTT Lemma 5.3, prime powers/collisions, and mass-preserving telescoping. |
| Theorem 3.2 | `t:relative-selector-comparison` | Uniform smooth-modulus comparison with the constant μ_F. Uses Proposition 4.1, Lemmas 4.4 and 4.5, scalar part of Proposition 4.3, KMTT Proposition 3.3 and elementary Fourier estimates. |
| Proposition 4.1 | `p:high-order-relative-prime` | Uniform full Gowers bound for Λ_q−1 on the larger scale window (not just at the natural M), plus first moment. KMTT Lemmas 2.2, 3.1, 4.3(i); Banks's zero-free bound; monotonicity. |
| Theorem 4.2 | `t:main` | Arbitrary bounded weight is tested against polynomial phases, on long integer intervals intersected with a congruence class of step q^b. Two spatial inputs use Fourier inversion and the whole parameter interval; longer families use Lemma 5.1, dual substitution and deletion of boundary-crossing parameters. |
| Proposition 4.3 | `p:heisenberg-phase` | Three claims: scalar nilmanifold equidistribution, polynomial-twist cancellation for zero vertical mean, and centered cutoff-free circle-selector cancellation. Uses Lemma 6.1, Green–Tao Theorem 2.9, polynomial coefficient approximation and summation by parts. Keep parameters a uniform over all integers; K has a lower bound only. |
| Lemma 4.4 | `l:unweighted-selector-relative-range` | Arbitrary savings in w for the centered selector count. Uses Theorem 4.2, Proposition 4.3 and smooth q, so r_j>w and r_j∤q^{b+1}. |
| Lemma 4.5 | `l:vertical-mode-multiplier` | S≥3 localized mode is a U^S multiplier with norm at most the Fourier absolute sum of the horizontal cutoff. The proof factors into exact cube cancellation and Fourier expansion. State nonempty interval, consistent with the denominator. |
| Lemma 5.1 | `p:localinverse` | Local phases correlating with each shifted input, or small scale. Uses KMTT Lemma 3.4 on differenced unweighted inputs, rational frequency selection and Plancherel. |
| Lemma 6.1 | `l:heisenberg-horizontal` | The selected denominator outruns every logarithmic power and gives uniform horizontal lower bound for coprime steps up to X^{1/5000}, logarithmically bounded nonzero frequency pair, and badly approximable α. Elementary Diophantine and scale inequalities. |
| Proposition 6.2 | `p:prime-phase` | Prime-weighted centered selector cancellation with arbitrary log saving on each stated polylogarithmic-modulus progression. Uses Lemma 4.5, Proposition 4.3, KMTT Lemma 3.1, Banks, Mertens and fundamental sieve lemma. The manuscript uses the Cramér model and a sieve, with no Vaughan/Type-II step. |
| Proposition 7.1 | `p:ergodic-comparison` | Summable log-saving L¹ norm, a.e. convergence of centered Λ-weighted difference, and zero limit for normalized prime comparison. Uses Proposition 6.2 at q=1, Teräväinen Theorem 4.1, orbit transference and PNT/partial summation. |
| Proposition A.1 | `p:separating-family` | Construct scales with lower bound for global quadratic-phase norm, arbitrary log savings on local tests, and nondecaying full Gowers norm. Uses Proposition 4.3, Lemma 4.5, bad approximability, Weyl and van der Corput. The comparison with fixed-family dilation subsequently uses Teräväinen and Theorem 4.2. |

Principal unnumbered dependencies include the affine lift of both shifts and selected prime, positive unweighted model count, higher-prime-power/collision bound, the local inverse localization and dual phase replacement, Heisenberg right-lattice invariance and vertical Haar integration on its chart, the filtered-circle product obstruction, partial-sum bounds on the dilated orbit, Fourier truncation and sieve midpoint, bounded-representative common conull set, and both routes from Mangoldt to primes. Substantial independent claims include density of the admissible β, the stronger-Liouville obstruction, the rotation extension for linear Bohr weights and its counterexample to preservation of the limit, the Green–Tao discussion, and the fixed-shift dilation calculation in Appendix A.

## Necessary manuscript repairs

### Corollary 1.5 proof input indexing

At `e:prodidentity` replace:

```tex
and take $G_i(x,u,v)=f_i(x)$ for $i\geq3$.
```

with:

```tex
and take $G_i(x,u,v)=g_i(x)$ for $i\geq3$.
```

The preceding sentence defines each `g_i` in the enlarged and reordered family. For example, if the original family consists only of `P_1(n)=n^3`, the enlarged degree-three input is `g_3=f_1`, whereas `f_3` is undefined. If the proof is written directly with the certified prime-phase estimate instead of product systems, label that as an alternative proof.

### Local Fourier multiplier domain

Lemma 4.5 divides by an interval cube count. Replace `let $I$ be a finite interval of integers` with `let $I$ be a finite nonempty interval of integers`. All applications use a nonempty I. Likewise, any Lean interface for phase testing should use a nonempty progression or make clear that the stated asymptotic size already implies nonemptiness.

### Scale choices and representative details

In the introductory overview, replace `a lacunary subsequence` with `an increasing subsequence whose consecutive ratios tend to one`. The actual sequence is `H_j=\lfloor\exp(j^{1/3})\rfloor`, increasing eventually, with `H_{j+1}/H_j\to1`. The pointwise proof correctly requires close spacing, and altering the rates to a fixed geometric ratio would invalidate its displayed gap estimate.

In the first paragraph of the proof of Proposition 7.1, insert:

```tex
Work with bounded measurable representatives, or restrict to the common
conull set on which the bounds for the $f_i$ hold at every integer
iterate of $T$.
```

This justifies all pointwise deterministic error bounds while preserving the domain of essential boundedness.

In the sieve application in Proposition 6.2, the displayed two bounds with `(\log X)^{-A'}` immediately preceding the test against `g` can be stated with exponent `-A'-2`, matching the bound in the next display. The fundamental lemma provides an error smaller than every fixed inverse logarithmic power. No extra hypothesis is needed.

## Editorial notices and comparison details

- In the introduction's linear rotation extension, add `and relabelling the polynomials and inputs` after adjoining the linear iterate, which explains why the displayed product identities use the original symbols.
- The horizontal lemma is written for `v≥1`. Proposition 4.3 uses natural numbers and `r_j∤v`, already excluding zero even in a convention with zero in ℕ. Its length lower bound implies positive K. Proposition 6.2 explicitly saying that P is nonempty would clarify the premise used by the average, although nonemptiness follows uniformly for sufficiently large N.
- The circular interval J should be represented as a proper open arc with measure in (0,1), including arcs through the coordinate seam. An implementation taking only intervals wholly inside (0,1) would restrict the manuscript theorem.
- The proof of Theorem 3.2 cites KMTT Proposition 3.3 with one extra function indexed as the anchor. There are k−1 shifted functions here. The result is uniform even for unbounded weight Λ_q−1.
- The proof of Proposition 4.1 uses x-scale N for the Cramér cutoff and ambient interval Y=qM+1 for the Gowers approximation. KMTT Lemma 3.1 explicitly allows these to differ. KMTT Lemma 2.2 with N_dilation=qM, b=1 gives exactly the U-norm on [1,qM+1]. KMTT Lemma 4.3(i) uses N as its scale and J=[M].
- The `N^{1/d-o(1)}` for M is uniform only under the stated restrictions on q, and the floor should be handled before taking logarithms. An exact equivalent for Lean is `M^d q^{d-1}≤N<(M+1)^d q^{d-1}` when d,q≥1. Section 5's assertion of large V_i uses the absorption of q-powers only after exhibiting a fixed polynomial dependence on q/δ.
- Proposition 3.1 takes M at its full natural scale. KMTT Lemma 5.3 (5.28) supplies the atom lower bound at that M. The factor `exp(-d sqrt(log M))` in KMTT Lemma 5.4 comes from a distinct shortening step in their prime-weight proof and does not belong to Proposition 3.1.
- Proposition 4.3's transfer to dilated orbits uses `D_s` on the quotient and `D_{1/s}` on group elements only. Both the Haar-fibre calculation and the horizontal Diophantine estimate are needed to justify the transfer. The size cap on the new step `v s d!` is why Lemma 6.1 has exponent 1/5000 and Proposition 4.3 has the smaller exponent 1/10000.
- For counting collision roots, using the cardinality of the root set over integers and a sum over the pairs is sufficient. The prime power contribution is bounded by √(qM+1) times two logarithmic factors divided by M; no prime number theorem is needed for this step.
- A strict half-length cutoff is sufficient for exact cube cancellation. The complete phase is affine-quadratic in cube coordinates only after each two-dimensional face has been checked. A mere scalar equidistribution statement does not supply this identity.
- The bracket algebra separates a quadratic term, a horizontal term and a carry. Near an integer m, the left/right-near cases of βn have distinct values of `m−floor(βn)`, and use the same upper bound `‖αn‖`. Replacing the carry by a constant changes behavior.
- In the first paragraph of §4, the duplicate reference to `e:firstsecondterms` and wording “the first inequality below … the second” can be cleaned up, as the displayed lines have already been combined.
- The sparse Green–Tao observation is an implication conditional on the measured relative density. The paper does not provide a quantitative asymptotic uniform over arbitrary shrinking J_N. Keep the implication distinct from its premise. [Teräväinen–Wang, arXiv:2603.09281v1, Theorem 1.1](https://arxiv.org/html/2603.09281v1) gives a piecewise threshold, `C_4(log log N)^{-c_4}` at k=4 and `C_k exp(−(log log log N)^{c_k})` at k≥5. The displayed common weaker threshold follows, but replace “for the constants in their theorem” by “for suitable constants depending only on k”, or state the sharper piecewise bound.

## Verified external-reference interfaces

- KMTT, arXiv:2608.19525v1, [full text](https://arxiv.org/html/2608.19525v1). Theorem 1.2 explicitly requires pairwise-distinct shifts. Lemma 3.4 assumes an unweighted count on [N] of size at least ρ, with M≤(N/q^{d−1})^{1/d}. It concludes the small-scale alternative or one common q′ and b and per-input bounded Lipschitz functions with correlation ≥ const·ρ^O(1)N. It does not give a local linear phase for an arbitrary weighted count. Lemma 5.3 assumes L(ceil(ε^{-A′}))|q, permits the full M-window, and yields local conditional expectations with error ≤ ε and atom resolution (5.28). Lemmas 2.2, 3.1, 4.3(i), Proposition 3.3 and Definition 2.3 were checked in the same version.
- Banks, arXiv:2610.15483v1, [Theorem 1.1](https://arxiv.org/html/2610.15483v1#S1.SS2), gives `(1−β) log r≥0.003` for real zeros in (0,1) of primitive real characters for every conductor r≥3 in its final assertion. The author's determinant estimate is for r≥10^10. The remainder uses the computation credited in that theorem. KMTT's cutoff condition is `(1−β) log Q̃≤0.001`; since r≤Q̃, the exclusion follows.
- Green–Tao, [Annals of Mathematics 175 (2012), Theorem 2.9](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf), produces a nonzero horizontal character and small `C^∞[K]`-norm from failure of `δ`-equidistribution of a polynomial orbit with rational Mal'cev basis. The [2014 erratum](https://annals.math.princeton.edu/wp-content/uploads/annals-v179-n3-p08-p.pdf) explicitly preserves this one-parameter result. The Heisenberg plus filtered-circle joint test is an application of this theorem, and covers and residue-class partial summation are original deductions.
- Iwaniec–Kowalski, *Analytic Number Theory*, §6.4, Fundamental Lemma 6.3, equations (6.43)–(6.48). The dimension condition follows by Mertens with a fixed dimension constant even with the primes dividing q removed. Its conclusion gives finite-support upper and lower sieve weights bounded by one, pointwise sandwich, and a gap decreasing faster than every inverse log power at the paper's cutoff. An author-hosted proof of a directly applicable alternative is [Koukoulopoulos, The Distribution of Prime Numbers, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf), parts (a)–(c). Chinese remainder, the midpoint bound against a complex function and large exceptional-prime divisor removal are application steps.
- Teräväinen, [arXiv:2401.03174v2, Theorem 4.1](https://arxiv.org/html/2401.03174v2), gives the fixed-family count divided by H^{d+1}, with bound `(H^{-1}+‖θ‖_{u^{d+1}[H]})^{1/K}`, support `[-C H^d,C H^d]` and bounded inputs and weight. It does not directly give the rescaled q-uniform conclusion of the present Theorem 4.2.
- Mirek–Wan–Wright, [arXiv:2505.15549v2, Theorem 1.1(ii)](https://arxiv.org/html/2505.15549v2), states a.e. Λ-weighted convergence for distinct-degree integer polynomials and exponents `1<q_i<∞`, `Σ 1/q_i≤1`. On a probability space `q_i=2ℓ` is valid for bounded inputs, including ℓ=1. Degrees are preserved on substituting P_i(n−1) and constant terms are permitted by MWW. The extraction of the prime-count normalization is a separate step. The pointwise result was numbered (i) in v1, so the version pin matters.
- The irrational-circle prime equidistribution used in Corollary 1.5 is classical Vinogradov. For the fixed β of this manuscript there is also an internal route: in the Cramér/sieve proof of Proposition 6.2, replace the nonzero vertical mode by the nonzero horizontal character `e(kβ(m−1))`; use its zero Haar mean in the scalar part of Proposition 4.3 and the ambient Gowers bound for linear twists. This reuses exactly the same cutoff and exceptional-divisor bookkeeping. It is an alternative derivation, and is distinct from the general introductory assertion for every irrational frequency.

## Division into substantial proof milestones

1. Common objects and exact identities. Coefficient scaling and affine lifts, integral orbit powers, right-lattice chart, floor carry and localized cube cancellation. These are independent of deep external inputs.
2. Discrete comparison and recurrence. Prove the local inverse reduction from KMTT Lemma 3.4, the local phase theorem, the horizontal and nilmanifold phase reduction, the smooth-prime comparison, and the weak-regularity iteration. Keep external propositions and manuscript-specific applications distinct.
3. Prime weighted phases, pointwise deductions and appendix. Apply Cramér/sieve, transfer to orbit averages, prove the log-saving subsequence/full sequence passages and selector normalization, then get bracket and separation results. Some algebraic subparts and finite averaging lemmas can be developed in parallel.

The proof was manually reviewed for mathematical dependencies and parameter ranges. This audit is independent of any Lean build. None of its manuscript-level deductions should be labelled kernel-checked on the basis of this file.

## Exact finite diagnostic

Run `python exact_selector_checks.py` using only Python's integral and rational arithmetic. The script checked the bracket-shift and floor-carry identities in 19,032 cases with `2≤denominator≤13`, `0<numerator<denominator`, four signed/zero rational α values and `−30≤n≤30`. It examined 320,705 three-dimensional cubes with `2≤denominator≤11`, all intermediate numerators, origin in `[−8,8]`, and step coordinates in `[−3,3]`. Of these, 45,051 had horizontal fractional parts of diameter strictly below one half. All their alternating phase sums were zero. In the unrestricted algebraic setting, the exact boundary case `β=1/4`, `α=2/3`, cube `n_ω=1+2|ω|`, has horizontal support in `[1/4,3/4]` and alternating phase sum `−16/3`. The rational test targets the general floor algebra and the importance of the strict diameter condition for unrestricted β. It does not test the Liouville approximation or any distribution estimate.
