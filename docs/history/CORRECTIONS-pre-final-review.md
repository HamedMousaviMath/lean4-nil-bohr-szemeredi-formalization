# Exact manuscript replacements

These patches apply to the [latest supplied LaTeX](../paper/current.tex). The latest source has the same numbered results as the initial source. The new display in Section 5 after the $i$th replacement already agrees with the checked argument and is retained.

[Download the corrected LaTeX](../paper/corrected.tex), or [apply the unified patch](../paper/lean-replacements.patch). The uploads remain preserved separately. The line numbers below refer to `paper/current.tex`.

## Mathematical and proof clarifications

### Remark 1.6, opening

Replace the passage at line 630.

```tex
At the smooth moduli considered here, the bound
```

With

```tex
At the moduli $q$ used in the density increment, which are divisible
by $\operatorname{lcm}(1,\ldots,w)$, the bound
```

The direct local-factor proof uses this divisibility to absorb its auxiliary divisor into a fixed power of the modulus. The wider smooth-modulus comparison still follows from Theorem 4.2.

### Preliminaries, before (11)

Replace the passage at line 713.

```tex
On a finite interval or arithmetic progression
```

With

```tex
On a finite nonempty interval or arithmetic progression
```

The normalized denominator in (11) must be positive.

### Preliminaries, before (12)

Replace the passage at line 725.

```tex
For a finite arithmetic progression \(P\), define
```

With

```tex
For a finite nonempty arithmetic progression \(P\), define
```

The average defining the ordinary-phase norm requires a nonempty progression.

### Lemma 4.5, opening

Replace the passage at line 1335.

```tex
Let \(S\geq3\), let \(I\) be a finite interval of integers, and let
```

With

```tex
Let \(S\geq3\), let \(I\) be a finite nonempty interval of integers, and let
```

This states the domain of the normalized norm explicitly. All applications already take nonempty intervals.

### Proposition 6.2, first sieve gap

Replace the passage at line 2692.

```tex
 \sum_{\ell\mid W}\frac{\lambda_\ell^+-\lambda_\ell^-}{\ell}
 \ll_{A'}(\log X)^{-A'}.
```

With

```tex
 \sum_{\ell\mid W}\frac{\lambda_\ell^+-\lambda_\ell^-}{\ell}
 \ll_{A'}(\log X)^{-A'-2}.
```

Choose the saving exponent in the fundamental lemma to match the error used in the complex-weight estimate.

### Proposition 6.2, midpoint error

Replace the passage at line 2705.

```tex
    (\lambda_\ell^+-\lambda_\ell^-)\frac{H_\ell}{H}
 \ll_{A'}(\log X)^{-A'}+\frac{\mathcal D}{H}.
```

With

```tex
    (\lambda_\ell^+-\lambda_\ell^-)\frac{H_\ell}{H}
 \ll_{A'}(\log X)^{-A'-2}+\frac{\mathcal D}{H}.
```

The local counting discrepancy contributes the same additive term. The sieve-gap term retains the chosen exponent.

### Section 7, before the definition of the averages

Replace the passage at line 2815.

```tex
For a Lipschitz function \(F:\mathbb T\to\mathbb C\), put
```

With

```tex
We choose bounded measurable representatives of the $f_i$, with
$|f_i(x)|\leq\|f_i\|_\infty$ everywhere. Since $T$ preserves measure,
these choices do not affect any of the averages outside the union
of the integer translates of the exceptional null sets.

For a Lipschitz function \(F:\mathbb T\to\mathbb C\), put
```

This single convention justifies the pointwise bounds and all almost-everywhere statements in Section 7 under the original essential supremum hypotheses.

### Proposition 7.1, start of proof

Replace the passage at line 2915.

```tex
By homogeneity assume that the \(f_i\) are \(1\)-bounded. Write
```

With

```tex
By homogeneity assume that the \(f_i\) are \(1\)-bounded. Relabel
the polynomials in increasing order of degree and permute the
corresponding inputs together with them. The products in the
averages and of the input norms are unchanged. Write
```

The relabelling permits the use of Teräväinen’s ordered fixed-family theorem and leaves the proposition valid for arbitrary order.

### Corollary 1.5, immediately before e:prodidentity

Replace the passage at line 3003.

```tex
and take $G_i(x,u,v)=f_i(x)$ for $i\geq3$.
```

With

```tex
and take $G_i(x,u,v)=g_i(x)$ for $i\geq3$.
```

The functions are indexed by the enlarged family. Above, its inputs were named $g_i$.

### Appendix A, before the difference-phase estimate

Replace the passage at line 3315.

```tex
For
\(1\leq v<H\), the geometric-series formula and bad approximability
give
```

With

```tex
For large \(j\) we have \(0<a_j<r_j\). For
\(1\leq v<H\), the geometric-series formula and bad approximability
give
```

Convergence to an interior value of the unit interval makes the integer multiplying the badly approximable number nonzero.

### Appendix A, comparison with KMTT Proposition 3.3

Replace the passage at line 3163.

```tex
The full Gowers norms of $G_q$ stay bounded below for $S\geq3$,
so the estimate of \cite[Proposition~3.3]{KMTT} gives no decay.
```

With

```tex
At every fixed order $S\geq3$, the full Gowers norm of $G_q$
stays bounded below. Thus the estimate from
\cite[Proposition~3.3]{KMTT}, at an order $S\geq3$ chosen using
Gowers monotonicity if necessary, gives no decay.
```

The proved lower bound starts at order three. The quoted proposition itself can supply order two.

## Presentation and citation corrections

### Introduction, shrinking-window progression threshold

Replace the passage at line 473.

```tex
among the selected primes up to $N$ whenever
\[
 \frac{\pi_{Z,J_N}(N)}{\pi(N)}
 > C_k\exp\bigl(-(\log\log\log N)^{c_k}\bigr)
\]
for the constants in their theorem.
```

With

```tex
among the selected primes up to $N$ for all sufficiently large
$N$ whenever
\[
 \frac{\pi_{Z,J_N}(N)}{\pi(N)}
 > C_k\exp\bigl(-(\log\log\log N)^{c_k}\bigr)
\]
for suitable constants $C_k,c_k>0$ depending only on $k$.
```

The stated common threshold is a consequence of the cited theorem. The theorem gives a stronger threshold for four terms.

### Introduction, pointwise proof overview

Replace the passage at line 623.

```tex
summable along a lacunary subsequence.
```

With

```tex
summable along an increasing subsequence whose consecutive
ratios tend to one.
```

The proof uses the integer parts of $\exp(j^{1/3})$, whose consecutive ratios tend to one.

### Section 4, immediately before e:high-order-gvn

Replace the passage at line 1389.

```tex
By \cite[Proposition~3.3]{KMTT} and Gowers monotonicity, we may
choose \(S\ge3\) so that the first inequality below holds for
every \(\nu\) and \(h\in\mathbb Z\). 
Lemma~\ref{l:vertical-mode-multiplier} implies
```

With

```tex
By \cite[Proposition~3.3]{KMTT} and Gowers monotonicity, choose a
common \(S\ge3\) for the weighted count estimate. Applying that
estimate and then Lemma~\ref{l:vertical-mode-multiplier} gives,
for every \(\nu\) and \(h\in\mathbb Z\),
```

The displayed inequality already combines the two inputs.

## Optional convention clarifications included in the corrected copy

### Definition of the return set (7)

Replace the passage at line 201.

```tex
\mathcal B_{Z,J}:=\{n\in\mathbb N:\{Z(n)\}\in J\},
```

With

```tex
\mathcal B_{Z,J}:=\{n\in\mathbb Z_{>0}:\{Z(n)\}\in J\},
```

This makes the return-set convention independent of whether natural numbers include zero. At zero the identity coset lies on the discarded seam. Every prime parameter is positive.

### Introduction, linear Bohr rotation extension

Replace the passage at line 385.

```tex
with the constant function $1$ if necessary, we may assume that
$P_1(n)=an$, with $a\ne0$.
```

With

```tex
with the constant function $1$ if necessary and relabelling the
polynomials and their inputs, we may assume that $P_1(n)=an$,
with $a\ne0$.
```

The linear term can occupy whichever position the original indexing gives it.

### Proof of Proposition 4.3, product nilmanifold

Replace the passage at line 2073.

```tex
\((H/\Gamma)\times\mathbb T\), equip the circle with its degree-\(d\)
filtration and consider the polynomial orbit
```

With

```tex
\((H/\Gamma)\times\mathbb T\), equip the circle with its degree-\(d\)
filtration and use the product filtration of degree \(\max(2,d)\).
Consider the polynomial orbit
```

This gives the filtration degree actually used by the application, including when the phase is linear.

## Revised passages already checked

- The new final lower bound after all shifted inputs have been replaced is precisely the output of `replace_shifted_inputs_by_phases`. Its use in the block-boundary argument is in `LocalPhaseSubstitution.lean`.
- The revised cross-reference before the selector comparison already includes the missing `e:firstterm` and has a single reference to `e:firstsecondterms`.
- The revised delimiters and alignment in the final count displays change only their presentation.
