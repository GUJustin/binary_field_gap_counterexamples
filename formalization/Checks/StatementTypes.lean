/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
import BinaryFieldCounterexamples.MainTheorems

/-!
Public-import and transitive axiom inventory. All main theorem proofs and
definitions must remain admission-free.
Run `python3 scripts/check_lean_contract_axioms.py` from the repository root to
enforce this boundary and detect missing declarations. The verified library's
endpoints are separately listed in Checks/Axioms.lean.
-/

#print axioms BinaryFieldCounterexamples.gaussianBinomial
#print axioms BinaryFieldCounterexamples.quadraticGaussian
#print axioms BinaryFieldCounterexamples.treeDenominator
#print axioms BinaryFieldCounterexamples.treeSupportCount
#print axioms BinaryFieldCounterexamples.avoidingTreeSupportCount
#print axioms BinaryFieldCounterexamples.agreementCount
#print axioms BinaryFieldCounterexamples.agreementGE
#print axioms BinaryFieldCounterexamples.agreementLE
#print axioms BinaryFieldCounterexamples.agreementEQ
#print axioms BinaryFieldCounterexamples.commonAgreementCount
#print axioms BinaryFieldCounterexamples.commonAgreementGE
#print axioms BinaryFieldCounterexamples.commonAgreementLE
#print axioms BinaryFieldCounterexamples.commonAgreementEQ
#print axioms BinaryFieldCounterexamples.badChallenges
#print axioms BinaryFieldCounterexamples.nonzeroBadChallenges
#print axioms BinaryFieldCounterexamples.ordinaryList
#print axioms BinaryFieldCounterexamples.additiveDomain
#print axioms BinaryFieldCounterexamples.mappedDomain
#print axioms BinaryFieldCounterexamples.affineDomain

/-! Public-import signatures synchronized with the strengthened Theorem 6.5.
The axiom inventory already contains these declarations; these checks also
print their current types through the reader-facing main-theorem import. -/
#check BinaryFieldCounterexamples.half_rate_trees_of_population
#check BinaryFieldCounterexamples.half_rate_decision_trees
#check BinaryFieldCounterexamples.half_rate_decision_trees_probability_of_finite
#check BinaryFieldCounterexamples.half_rate_decision_trees_probability
#check BinaryFieldCounterexamples.higher_rate_lengthening

/-! Longfellow affine seed, transfer, and concrete bounds. -/
#print axioms BinaryFieldCounterexamples.Longfellow.listSize
#print axioms BinaryFieldCounterexamples.Longfellow.listSize_value
#print axioms BinaryFieldCounterexamples.Longfellow.parameters
#print axioms BinaryFieldCounterexamples.Longfellow.parameters_4151
#print axioms BinaryFieldCounterexamples.Longfellow.parameters_4265
#print axioms BinaryFieldCounterexamples.Longfellow.parameters_4307
#print axioms BinaryFieldCounterexamples.Longfellow.parameters_4415
#print axioms BinaryFieldCounterexamples.Longfellow.parameterPairs
#print axioms BinaryFieldCounterexamples.Longfellow.configured_parameter_bounds
#print axioms BinaryFieldCounterexamples.Longfellow.exterior_pole_budget_4151
#print axioms BinaryFieldCounterexamples.Longfellow.exterior_pole_budget_4265
#print axioms BinaryFieldCounterexamples.Longfellow.exterior_pole_budget_4307
#print axioms BinaryFieldCounterexamples.Longfellow.exterior_pole_budget_4415
#print axioms BinaryFieldCounterexamples.Longfellow.central_interval_4151
#print axioms BinaryFieldCounterexamples.Longfellow.central_interval_4265
#print axioms BinaryFieldCounterexamples.Longfellow.central_interval_4307
#print axioms BinaryFieldCounterexamples.Longfellow.central_interval_4415
#print axioms BinaryFieldCounterexamples.Longfellow.probability_integer_certificate
#print axioms BinaryFieldCounterexamples.Longfellow.probability_lower_rational
#print axioms BinaryFieldCounterexamples.Longfellow.probability_lower
#print axioms BinaryFieldCounterexamples.Longfellow.exists_seed_family
#print axioms BinaryFieldCounterexamples.Longfellow.exists_exterior_polynomial_labels_injective
#print axioms BinaryFieldCounterexamples.Longfellow.exists_padded_pole_pair_of_polynomial_family
#print axioms BinaryFieldCounterexamples.longfellow_counterexample
#print axioms BinaryFieldCounterexamples.longfellow_counterexample_probability
