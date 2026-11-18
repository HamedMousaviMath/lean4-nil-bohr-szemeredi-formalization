# Final manuscript report

The author-supplied final LaTeX and PDF are preserved in `paper/current.tex` and `paper/current.pdf`. They are the basis of the paper map and both blueprints. The compiled LaTeX and supplied PDF agree in mathematical content and comprise 39 pages. The earlier source, its PDF and the proposed interim edits are in `paper/history/review/`.

## Changes reflected in the formalization

| Manuscript location | Final text and checked correspondence |
| --- | --- |
| Equation (7) | The Heisenberg return set explicitly uses positive integer times. The proof checks the open-window identity on that domain. |
| Remark 1.6 | The alternate local-factor proof is stated for the density-increment moduli, with `lcm(1,…,w) ∣ q`. This is the modulus condition in the checked argument. |
| Equations (11)–(12) and Lemma 4.5 | The normalization and multiplier statements specify nonempty domains. |
| Proposition 4.3 | The maximum-prefix bound on the cover is now equation (44). It is covered by `heisenbergCoverSequence_prefix_eq_scalarAverage` and `norm_heisenbergCoverSequence_prefix_le` and used in `twisted_heisenberg_log_saving`. The paper uses positive natural numbers. |
| Proposition 6.2 | Both sieve midpoint error displays use the saving with exponent `-A'-2`. The proof uses the sieve gap at that strength. |
| Section 7 and Proposition 7.1 | The manuscript states the bounded-representative convention and jointly relabels the polynomials and their inputs in the proof. The checked comparison accepts distinct positive degrees in arbitrary order. |
| Corollary 1.5 | The product rotation uses the reindexed inputs `g_i` for `i ≥ 3`. |
| Appendix A | The Weyl-difference argument makes the positivity of `a_j` explicit. The comparison with the weighted Gowers estimate specifies an order at least three. |
| Pointwise proof overview | The stated subsequence has consecutive ratios tending to one, as used in the all-scale extension. |

The new equation (44) shifts the former equations (44)–(61) to (45)–(62). The 19 numbered mathematical items retain their numbers. The paper map and blueprints use the final equation numbers, including (25)–(27) for the three progression estimates in Proposition 4.3. The canonical label ledger is `paper/labels.json`.

## Verification and scope

The release records one formalized definition, two results proved under their manuscript hypotheses and sixteen checked conditional deductions. The external results and the exact interfaces used in Lean are documented in `docs/ASSUMPTIONS.md` and `docs/EXTERNAL_INPUTS.json`. For the introductory shrinking-window application, the checked deduction uses Teräväinen–Wang in its stated large-scale domain and distinguishes the four-term estimate when choosing constants for the displayed common bound.

The production Lean sources and dependency pins are byte-identical to the clean build of 156 modules with the audit of 975 public theorems. The final release replays that build and reruns the project-wide axiom audit and the headline, blueprint and catalogue declaration checks. The audit uses only `propext`, `Classical.choice` and `Quot.sound`. The detailed logs are indexed in `evidence/README.md`.
