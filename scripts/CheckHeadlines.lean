import NilBohr

set_option pp.fullNames true

-- Corollary 1.1 and the four main results.
#check NilBohr.bohr_recurrence
#print axioms NilBohr.bohr_recurrence
#check NilBohr.heisenbergRecurrence_of_analytic_inputs
#print axioms NilBohr.heisenbergRecurrence_of_analytic_inputs
#check NilBohr.bracketRecurrence_of_analytic_inputs
#print axioms NilBohr.bracketRecurrence_of_analytic_inputs
#check NilBohr.heisenberg_pointwise_of_prime_model
#print axioms NilBohr.heisenberg_pointwise_of_prime_model
#check NilBohr.bracket_pointwise_of_prime_model
#print axioms NilBohr.bracket_pointwise_of_prime_model

-- Remark 1.6 on the moduli used by the density increment.
#check NilBohr.centeredSelectorComparison_on_lcm_moduli_of_obstructions
#print axioms NilBohr.centeredSelectorComparison_on_lcm_moduli_of_obstructions

-- Theorems 3.2 and 4.2 and Propositions 4.1, 4.3 and 6.2.
#check NilBohr.relativeSelectorComparison_of_obstructions
#print axioms NilBohr.relativeSelectorComparison_of_obstructions
#check NilBohr.high_order_relative_prime_of_analytic_inputs
#print axioms NilBohr.high_order_relative_prime_of_analytic_inputs
#check NilBohr.localGeneralizedVonNeumann_of_kmtt
#print axioms NilBohr.localGeneralizedVonNeumann_of_kmtt
#check NilBohr.heisenbergPhaseEstimates_of_quantitativeLeibman
#print axioms NilBohr.heisenbergPhaseEstimates_of_quantitativeLeibman
#check NilBohr.heisenbergPrimeLocalPhase_of_literature
#print axioms NilBohr.heisenbergPrimeLocalPhase_of_literature

-- Proposition 7.1 accepts distinct degrees in arbitrary order.
#check NilBohr.smoothErgodicComparison_of_prime_model_distinct_degrees
#print axioms NilBohr.smoothErgodicComparison_of_prime_model_distinct_degrees

-- Proposition A.1 and the count comparison that follows it.
#check NilBohr.appendixA_separating_family_of_quantitativeLeibman
#print axioms NilBohr.appendixA_separating_family_of_quantitativeLeibman
#check NilBohr.appendixA_count_comparison
#print axioms NilBohr.appendixA_count_comparison
