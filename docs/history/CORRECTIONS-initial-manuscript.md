# Manuscript replacements

The originals remain in `manuscript/`. The proposed changes below use the original labels and PDF numbering.

## Necessary

**Corollary 1.5, immediately before `e:prodidentity`.** Replace

```tex
and take $G_i(x,u,v)=f_i(x)$ for $i\geq3$.
```

with

```tex
and take $G_i(x,u,v)=g_i(x)$ for $i\geq3$.
```

The functions are indexed by the enlarged family. If the only original polynomial is of degree three, for instance, the correct function in position three is the original first input.

**Lemma 4.5.** Replace

```tex
let $I$ be a finite interval of integers
```

with

```tex
let $I$ be a finite nonempty interval of integers
```

The norm is divided by the norm of the interval indicator. All applications already have nonempty intervals.

**Overview of the proofs, pointwise subsection.** Replace

```tex
summable along a lacunary subsequence
```

with

```tex
summable along an increasing subsequence whose consecutive ratios tend to one
```

The actual subsequence $H_j=\lfloor\exp(j^{1/3})\rfloor$ has ratios tending to one. The proof uses the closely spaced sequence to control the gaps.

**Proposition 7.1, proof, immediately after the homogeneity reduction.** Insert

```tex
Work with bounded measurable representatives, or restrict to the common
conull set on which the bounds for the $f_i$ hold at every integer
iterate of $T$.
```

This justifies the uniform pointwise bounds without strengthening $L^\infty$ to a pointwise bounded representative requirement.

**Proposition 6.2, sieve midpoint.** In the two displayed sieve-gap bounds just before testing against $g$, replace the power `-A'` by `-A'-2`, to match the power already used in the following display. The fundamental lemma supplies arbitrary logarithmic saving.

**Introduction, shrinking-window Green--Tao implication.** Replace

```tex
for the constants in their theorem.
```

with

```tex
for suitable constants depending only on $k$.
```

The common displayed threshold follows from Teräväinen--Wang, but their Theorem 1.1 states a stronger separate threshold for $k=4$. Alternatively display that separate threshold.

**Remark 1.6, opening scope.** Replace

```tex
At the smooth moduli considered here,
```

with

```tex
At the moduli of the density increment, where $\mathcal L(w)\mid q$,
```

The fixed-power argument uses divisibility by the auxiliary denominator. The density-increment condition already supplies that divisor through the least common multiple. The wider smooth range of Theorem 3.2 uses only primorial divisibility and does not give this fixed-power step by the same argument. For instance, if q is eight times the primorial, the exponent of three in q is one. For any fixed B, the admissible size bound on the auxiliary denominator can allow three to the power B+1 as w grows, which need not divide the fixed power q^B.

## Optional

- In (7), change `$n\in\mathbb N$` to `$n\in\mathbb Z_{>0}$` to make the return-set statement independent of the convention for natural numbers. If zero is included, the formula for $\mathcal B_{Z,J}$ includes it when $0\in J$, whereas the open window excludes the identity coset on the horizontal seam. All shifted-prime parameters are already positive.
- In Section 4, remove the repeated reference to `e:firstsecondterms`, and replace the sentence introducing “the first inequality … the second” with a sentence explaining that the single displayed estimate combines KMTT Proposition 3.3 and the multiplier lemma.
- In the linear Bohr rotation extension, explicitly say that the polynomials and inputs are relabelled after a linear iterate is adjoined.
- In the application of Green--Tao to the product with a degree-$d$ circle, name the product filtration degree $\max(2,d)$. This makes the $d=1$ case transparent.

- In Appendix A, replace `since \(a_j<r_j\) and` with `since \(0<a_j<r_j\) for large \(j\) and`. The lower inequality follows from convergence of the approximants to \(\beta\in(0,1)\) and ensures the difference-phase coefficient is nonzero.
- In the Appendix A comparison with the KMTT estimate, specify “at any chosen order \(S\ge3\)” when invoking the lower bound in Proposition A.1. KMTT Proposition 3.3 permits order two.
