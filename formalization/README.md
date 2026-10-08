# Lean formalization

This directory contains the Lean 4 development for the paper. It proves every
theorem, proposition, corollary and lemma of the paper, the remarks and
numerical bounds derived from them, and the finite arithmetic behind the
concrete Binius64 and Longfellow bounds. The [Coverage](#coverage) section maps
each statement of the paper to the Lean declarations that prove it.
[Scope](#scope) states what lies outside the formalization. Reusable results
are intended for ArkLib; paper-specific constructions and theorem assembly stay
here.

The library `BinaryFieldCounterexamples` has 3135 public declarations. All are
proved without `sorry`, and their transitive axiom reports contain only Lean's
standard `propext`, `Classical.choice` and `Quot.sound`. There are no custom
axioms or vendored libraries.

## Build

Install [elan](https://github.com/leanprover/elan), then run from the
repository root:

```sh
cd formalization
lake exe cache get
lake build
```

Lake uses Lean **4.34.0**, as specified in `lean-toolchain`, and ArkLib
[`fa14552d40e793f2ea26e65c440306aae0c08a26`](https://github.com/Verified-zkEVM/ArkLib/tree/fa14552d40e793f2ea26e65c440306aae0c08a26).
The committed `lake-manifest.json` pins all transitive dependencies. The default
targets are the root `BinaryFieldCounterexamples` and
`BinaryFieldCounterexamples.MainTheorems`, which imports the 50 reader-facing
main-theorem modules. Expected result: `Build completed successfully (4461 jobs)`,
with no `sorry` warnings.

## Coverage

File paths are relative to `BinaryFieldCounterexamples/`. Declaration names are
given without namespace prefixes; each file opens its namespaces at the top.
Statement numbers and pages are those of the compiled PDF. Where a statement is
proved by one declaration and a companion that adds further clauses of the
printed statement, both are listed.

### Numbered statements

| Paper statement | Lean declarations | File |
|---|---|---|
| [Lemma 3.9, p. 21](../binary-field-counterexamples.pdf#page=21). Leading coefficients determine the subspace | `eq_of_subspacePolynomial_nonleading_prefix_eq` | `Polynomial/LocatorPrefixInjectivity.lean` |
| [Lemma 3.10, p. 22](../binary-field-counterexamples.pdf#page=22). Inner polynomials of additive compositions | `isAdditivePolynomial_of_comp`, `exists_rootAddSubgroup_of_additive_comp`; `subspacePolynomial_additive_composition_inner` | `Polynomial/AdditiveComposition.lean`; `Polynomial/SectionThreeAdditivity.lean` |
| [Lemma 3.11, p. 22](../binary-field-counterexamples.pdf#page=22). From common high coefficients to a received line | `poleReduction_full`, `normalizedPoleReduction_full`, `polynomialOverPole_full`; `poleReduction_agreementGE`, `poleReduction_badChallenge`; `agreementEQ_polynomialOverPole`, `commonAgreementEQ_polynomialOverPole_right` | `Constructions/PoleReductionFull.lean`; `Constructions/PoleReduction.lean`; `Constructions/Gold/PaddingPolynomials.lean` |
| [Lemma 3.12, p. 23](../binary-field-counterexamples.pdf#page=23). Equal individual and common agreement | `source_conversion_agreements`; `agreementGE_source_conversion_iff`, `badChallenges_source_conversion_eq`, `source_conversion_exceptional_probability_le` | `Agreement/SourceConversion.lean`; `Agreement/SourceConversionConverse.lean` |
| [Lemma 3.13, p. 24](../binary-field-counterexamples.pdf#page=24). Two individually far inputs | Binary case: `agreementLE_binaryQuarterSource`, `badChallenges_binaryQuarterSource_eq_image`; `arbitrary_padded_binaryQuarterSources`, `arbitrary_padded_binaryQuarterSources_affine`. General prime power: `agreementLE_submoduleQuarterSource`; `affine_primePowerQuarterSource_full` | `Constructions/ExactHalfAgreement/SourceBound.lean`; `Constructions/Gold/ArbitraryPaddingSourceBound.lean`; `Constructions/QuadraticForms/DomainSource.lean`; `Constructions/QuadraticForms/AffineQuarterSource.lean` |
| [Lemma 3.16, p. 25](../binary-field-counterexamples.pdf#page=25). From Boolean polynomials to witnesses | `boolean_to_witness_mapped`, `mappedBooleanWitnessLabel_eq_iff` | `Constructions/NearUnit/BooleanWitnessMapped.lean` |
| [Lemma 3.18, p. 26](../binary-field-counterexamples.pdf#page=26). Balanced padding | `exists_balanced_fixedSize_padding`; `exists_balanced_fixedSize_padding_full` | `Counting/BalancedPadding.lean`; `Counting/SectionThreeCompanions.lean` |
| [Lemma 3.19, p. 27](../binary-field-counterexamples.pdf#page=27). Collision averaging | `exists_parameter_image_card_bounds`; `exists_parameter_image_card_rational_bounds` | `Counting/CollisionAveraging.lean`; `Counting/RationalCollision.lean` |
| [Theorem 4.1, p. 28](../binary-field-counterexamples.pdf#page=28). Quadratic count at rate 1/16 | `quadratic_near_johnson_exact`, `quadratic_near_johnson_both_far_exact`; `quadratic_near_johnson_exact_with_decoding_list`, `quadratic_near_johnson_at_largest_below_johnson` | `MainTheorems/QuadraticNearJohnsonExact.lean`; `MainTheorems/QuadraticNearJohnsonFull.lean` |
| [Corollary 4.2, p. 30](../binary-field-counterexamples.pdf#page=30). Any finite field containing the evaluation domain | `quadratic_near_johnson_same_field`, `quadratic_near_johnson_full_field`; `quadratic_near_johnson_same_field_full` | `MainTheorems/QuadraticNearJohnsonCompanions.lean`; `MainTheorems/QuadraticNearJohnsonFull.lean` |
| [Lemma 4.3, p. 31](../binary-field-counterexamples.pdf#page=31). Unpadded locator construction | `unpadded_codimension_collision_counterexample`, `unpadded_codimension_counterexample` | `MainTheorems/UnpaddedCodimension.lean` |
| [Corollary 4.4, p. 32](../binary-field-counterexamples.pdf#page=32). Cubic count at rate 1/32 | `cubic_count_rate_one_thirtytwo` | `MainTheorems/UnpaddedCodimension.lean` |
| [Theorem 4.5, p. 33](../binary-field-counterexamples.pdf#page=33). Every fixed rate on every additive domain | `all_rates_certain_failure`; `all_rates_certain_failure_full`; `all_rates_certain_failure_polynomial_count`, `all_rates_certain_failure_quadratic_count` | `MainTheorems/AllRatesCertainFailure.lean`; `MainTheorems/AllRatesCertainFailureFull.lean`; `MainTheorems/AllRatesPolynomialCount.lean` |
| [Corollary 4.6, p. 34](../binary-field-counterexamples.pdf#page=34). Rate 1/8 at finite length | `rate_eighth_finite`, `rate_eighth_finite_count`; `rate_eighth_finite_probability` | `MainTheorems/RateEighthFinite.lean`; `MainTheorems/RateEighthProbability.lean` |
| [Theorem 4.7, p. 35](../binary-field-counterexamples.pdf#page=35). Hyperplanes at half agreement | `exact_half_agreement`; `exact_half_agreement_full` | `MainTheorems/ExactHalfAgreement.lean`; `MainTheorems/ExactHalfAgreementProbability.lean` |
| [Theorem 5.1, p. 36](../binary-field-counterexamples.pdf#page=36). The Gold counting bound | `gold_counting_list`, `gold_counting`, `gold_counting_sharp`; `gold_counting_list_fullSource`, `gold_counting_sharp_fullSource`; `gold_counting_sharp_affine_translate` | `MainTheorems/GoldCounting.lean`; `MainTheorems/GoldCountingFullSource.lean`; `MainTheorems/AffineTranslateExamples.lean` |
| [Corollary 5.2, p. 37](../binary-field-counterexamples.pdf#page=37). Dense additive domains | `superpolynomial_near_johnson`; `superpolynomial_near_johnson_small_codimension`; `superpolynomial_near_johnson_every_larger_extension` | `MainTheorems/SuperpolynomialNearJohnson.lean`; `MainTheorems/DenseSmallCodimension.lean`; `MainTheorems/LargerExtensionNearJohnson.lean` |
| [Corollary 5.3, p. 38](../binary-field-counterexamples.pdf#page=38). Fixed extension degree | `gold_fixed_extension_probability`; `gold_full_field_fixed_extension_probability` | `MainTheorems/FixedExtensionGold.lean`; `MainTheorems/FullFieldExtensionGold.lean` |
| [Theorem 5.4, p. 38](../binary-field-counterexamples.pdf#page=38). No fixed polynomial exceptional bound below Johnson | `no_fixed_polynomial_exceptional_bound_optimal_exponent`; `optimal_fixed_threshold_of_exponent` | `MainTheorems/OptimalFixedThreshold.lean`; `Constructions/Gold/OptimalFixedThreshold.lean` |
| [Lemma 5.5, p. 39](../binary-field-counterexamples.pdf#page=39). Labels of linear functions | `functionalPolynomial_eval`, `eq_functionalPolynomial`; `parameterPolynomial_artinSchreier`, `parameterEquiv`, `card_parameterDomain`; `parameterPolynomial_degree_and_leadingCoeff` | `Constructions/Gold/FunctionalInterpolants.lean`; `Constructions/Gold/Parameters.lean`; `Constructions/Gold/LabelsFull.lean` |
| [Lemma 5.6, p. 40](../binary-field-counterexamples.pdf#page=40). The polynomial of a quadratic function | `quadraticPolynomial_properties`; `repairedPolynomial_derivative`, `repairedPolynomial_artinSchreier`; `tensorPolynomial_radical_iff` | `Constructions/Gold/LabelsFull.lean`; `Constructions/Gold/Repairs.lean`; `Constructions/Gold/Polar.lean` |
| [Lemma 5.8, p. 41](../binary-field-counterexamples.pdf#page=41). Moment equations and the coefficients of J | `gold_moment_window_iff` | `Constructions/Gold/MomentWindowIff.lean` |
| [Lemma 5.9, p. 42](../binary-field-counterexamples.pdf#page=42). Rank under the moment equations | `tensorPolarRank_lower_bound_of_moments`; `tensorLinearPart_endpoint_coefficients`; `gold_rank_degree_full` | `Constructions/Gold/MinimumRank.lean`; `Constructions/Gold/Saturation.lean`; `Constructions/Gold/RankDegreeFull.lean` |
| [Lemma 5.10, p. 42](../binary-field-counterexamples.pdf#page=42). Level sets of a quadratic function | `mem_repairs_iff`, `card_repairs_of_polarRank`, `exists_bit_zeroCount_of_polarRank`; `quadraticRepair_add_radical` | `Constructions/Gold/QuadraticCharacters.lean`; `Constructions/Gold/PaddingRadicals.lean` |
| [Lemma 5.12, p. 43](../binary-field-counterexamples.pdf#page=43). Gold moments give polynomials with many roots | `gold_locators_full`; `repairedLocator_fullSource_natDegree`; `exists_repairedLocator_family`; `repairedLocator_properties`; `repairedLocator_injective_parameters`; `card_mapped_repairedLocator_collisions_le` | `Constructions/Gold/CompleteLocators.lean`; `Constructions/Gold/FullSource.lean`; `Constructions/Gold/Family.lean`; `Constructions/Gold/LocatorWitness.lean`; `Constructions/Gold/Distinctness.lean`; `Constructions/Gold/Collisions.lean` |
| [Lemma 5.13, p. 44](../binary-field-counterexamples.pdf#page=44). Rank-2t solutions of the moment equations | `card_momentTensors_lower_bound`, `card_momentTensors_eq_rank_kernel`; `alternatingCode_minimumRank_count_lower_bound` | `Constructions/Gold/MomentPopulation.lean`; `Constructions/Gold/MinimumRankPopulation.lean` |
| [Lemma 5.14, p. 46](../binary-field-counterexamples.pdf#page=46). Adding an additive set of common roots | `exists_pole_padding_exact`; `binarySubspacesOfCard_spanning_probability`; `paddingRetentionProbability_product` | `Constructions/Gold/PaddingAssembly.lean`; `Constructions/Gold/ExactRetention.lean`; `Constructions/Gold/ExactRetentionProbability.lean` |
| [Corollary 5.15, p. 46](../binary-field-counterexamples.pdf#page=46). Gold families at rate 1/2 | `gold_half_rate_sharp`; `gold_half_rate_dense_asymptotic` | `MainTheorems/Native128Example.lean`; `MainTheorems/DenseHalfRate.lean` |
| [Corollary 5.16, p. 47](../binary-field-counterexamples.pdf#page=47). Higher rates on every dense binary domain | `higher_rate_lengthening`, `higher_rate_lengthening_gap`; `higher_rate_lengthening_full`, `higher_rate_lengthening_lt_sqrt`, `higher_rate_lengthening_rate_coverage` | `MainTheorems/HigherRateLengthening.lean`; `MainTheorems/HigherRateLengtheningFull.lean` |
| [Corollary 5.17, p. 48](../binary-field-counterexamples.pdf#page=48). Every fixed rate on every dense binary domain | `gold_all_rates`, `gold_all_rates_translate`, `gold_all_rates_limiting_fraction` | `MainTheorems/GoldAllRates.lean` |
| [Corollary 5.18, p. 49](../binary-field-counterexamples.pdf#page=49). A 128-bit-field example | `native128Example_sharp`; `native128Example_sharp_affine_translate` | `MainTheorems/Native128Example.lean`; `MainTheorems/AffineTranslateExamples.lean` |
| [Corollary 5.19, p. 50](../binary-field-counterexamples.pdf#page=50). Longfellow's version-7 codes | `longfellow_counterexample_probability`; `longfellow_specification_power_basis`, `longfellow_specification_minimal_common_agreement` | `MainTheorems/Longfellow.lean`; `MainTheorems/LongfellowSpecification.lean` |
| [Proposition 5.21, p. 52](../binary-field-counterexamples.pdf#page=52). The trace family | `traceRankFamily_card_lower`; `translatedTracePolynomial_zero_card_of_exact_rank`; `traceFamilyPolynomial_derivative`; `traceFamily_parameters_eq_of_polarBilin_eq`; `traceFamilyQuadraticForm_dilate`; `IsElliptic`, `traceRankFamily_elliptic_card_lower`, `IsElliptic.zero_natCard`, `traceQuadraticFamily_dilation_full` | `Constructions/QuadraticForms/TracePopulation.lean`; `Constructions/QuadraticForms/TraceDegree.lean`; `Constructions/QuadraticForms/TracePolynomial.lean`; `Constructions/QuadraticForms/TraceRadical.lean`; `Constructions/QuadraticForms/TraceDilation.lean`; `Constructions/QuadraticForms/EllipticType.lean` |
| [Theorem 5.22, p. 53](../binary-field-counterexamples.pdf#page=53). Quadratic-form families on full fields and hyperplanes | `quadratic_forms_list`, `quadratic_forms_near_johnson_sharp` | `MainTheorems/QuadraticForms.lean` |
| [Corollary 5.23, p. 55](../binary-field-counterexamples.pdf#page=55). Decoding lists approaching Johnson | `ordinary_lists_near_johnson`, `ordinary_lists_near_johnson_finite` | `MainTheorems/OrdinaryListAsymptotics.lean` |
| [Corollary 5.24, p. 56](../binary-field-counterexamples.pdf#page=56). Every fixed rate on dense binary domains | `dense_all_rates`; `dense_all_rates_rate_coverage` | `MainTheorems/DenseAllRates.lean`; `MainTheorems/DenseRateCoverage.lean` |
| [Lemma 6.1, p. 58](../binary-field-counterexamples.pdf#page=58). Unions of flats give exceptional challenges | `flats_to_challenges`, `flats_to_challenges_rational`; `flats_to_challenges_binary_full` | `Constructions/Trees/FlatsToChallenges.lean`; `Constructions/Trees/FlatsToChallengesFull.lean` |
| [Lemma 6.4, p. 60](../binary-field-counterexamples.pdf#page=60). Structure of tree functions | `tree_structure`; `isTreeFunction_affineEquiv_iff`, `isTreeFunction_quotient_iff`; `isTreeFunction_two_count` | `Constructions/Trees/Intrinsic/TreeDegree.lean`; `Constructions/Trees/Intrinsic/Structure.lean`; `Constructions/Trees/Intrinsic/Counts.lean` |
| [Lemma 6.5, p. 61](../binary-field-counterexamples.pdf#page=61). The root functional is unique | `tree_root_unique`, `isTreeRoot_iff_degree` | `Constructions/Trees/Intrinsic/DegreeStructure.lean` |
| [Lemma 6.6, p. 61](../binary-field-counterexamples.pdf#page=61). Counting tree functions | `isTreeFunction_count_full`; `isTreeFunction_count`, `isTreeFunction_count_gaussian`, `intrinsicTreeSupportCount_growth` | `Constructions/Trees/Intrinsic/CountingFull.lean`; `Constructions/Trees/Intrinsic/Counts.lean` |
| [Corollary 6.7, p. 61](../binary-field-counterexamples.pdf#page=61). Half agreement on the whole domain | `half_agreement_trees`, `half_agreement_trees_asymptotic`; `half_agreement_trees_intrinsic`, `half_agreement_trees_asymptotic_intrinsic`; `half_agreement_trees_full` | `MainTheorems/HalfRateDecisionTrees.lean`; `MainTheorems/IntrinsicTrees.lean`; `MainTheorems/IntrinsicAvoidingTrees.lean` |
| [Lemma 6.9, p. 62](../binary-field-counterexamples.pdf#page=62). Counting tree supports that avoid a subspace | `isAvoidingTree_count_full`, `isAvoidingTree_iff_avoidingTreeFamily`; `avoidingTreeFamily_card`; `avoidingTreeSupportCount_growth` | `Constructions/Trees/Intrinsic/Avoiding.lean`; `Constructions/Trees/AvoidingCounts.lean`; `Counting/TreeAsymptotics.lean` |
| [Theorem 6.10, p. 63](../binary-field-counterexamples.pdf#page=63). Decision-tree construction at rate 1/2 | `half_rate_decision_trees`, `half_rate_decision_trees_probability`; `half_rate_support_count_asymptotic`; `half_rate_decision_trees_intrinsic_full`, `half_rate_decision_trees_probability_intrinsic_full` | `MainTheorems/HalfRateDecisionTrees.lean`; `MainTheorems/TreeSupportAsymptotics.lean`; `MainTheorems/IntrinsicAvoidingTrees.lean` |

### Definitions

[PaperSemantics.lean](BinaryFieldCounterexamples/PaperSemantics.lean) fixes the
meaning of agreement, common agreement, exceptional challenges and decoding
lists in terms of actual polynomial evaluations.

| Paper definition | Lean definitions | File |
|---|---|---|
| [Definition 3.1, p. 18](../binary-field-counterexamples.pdf#page=18). Reed–Solomon code and received words | No separate declaration. Words are functions `D → F`; codewords are evaluations of polynomials with `degree < K`, as in `agreementCount` and `agreementGE` | `PaperSemantics.lean` |
| [Definition 3.2, p. 18](../binary-field-counterexamples.pdf#page=18). Individual and common agreement | `agreementCount`, `agreementGE`, `agreementLE`, `agreementEQ`; `commonAgreementCount`, `commonAgreementGE`, `commonAgreementLE`, `commonAgreementEQ` | `PaperSemantics.lean` |
| [Definition 3.3, p. 19](../binary-field-counterexamples.pdf#page=19). Received line and exceptional challenges | `badChallenges`, `nonzeroBadChallenges` | `PaperSemantics.lean` |
| [Definition 3.4, p. 19](../binary-field-counterexamples.pdf#page=19). Explaining polynomials, witnesses, and decoding lists | `ordinaryList` | `PaperSemantics.lean` |
| [Definition 3.5, p. 19](../binary-field-counterexamples.pdf#page=19). Agreement thresholds and gaps | `johnsonCoordinateThreshold`, `johnsonAgreementDeficit`, `paperCommonAgreementGap`, `individuallyFarAtTarget`; bridges `paperIndividualAgreement_eq_iff`, `paperCommonAgreement_eq_iff`, `paperCommonAgreementGap_of_exact`, `individuallyFarAtTarget_iff_not_agreementGE` | `Agreement/ThresholdGaps.lean` |
| [Definition 3.6, p. 20](../binary-field-counterexamples.pdf#page=20). Canonical polynomial representative | `canonicalRepresentative` | `Polynomial/SectionThreeCanonical.lean` |
| [Definition 3.7, p. 21](../binary-field-counterexamples.pdf#page=21). Additive domains and affine flats | `additiveDomain`, `affineDomain`, `mappedDomain` | `PaperSemantics.lean` |
| [Definition 3.8, p. 21](../binary-field-counterexamples.pdf#page=21). Locators and linearized polynomials | `subspacePolynomial`; `affineFlatLocator`; `IsBinaryLinearized`; `IsQLinearized`; `IsAdditivePolynomial` | `Polynomial/SubspacePolynomial.lean`; `Polynomial/AffineFlatLocators.lean`; `Polynomial/BinarySupport.lean`; `Polynomial/PrimePowerSupport.lean`; `Polynomial/AdditiveComposition.lean` |
| [Definition 3.14, p. 25](../binary-field-counterexamples.pdf#page=25). Boolean functions, supports, and balance | Boolean functions are maps `U → ZMod 2`. `binarySupport`; `IsBalanced`. Boolean polynomials have no separate declaration; the condition is a hypothesis of `boolean_to_witness_mapped` | `Constructions/Trees/SupportFamily.lean`; `Constructions/Trees/Intrinsic/Definition.lean`; `Constructions/NearUnit/BooleanWitnessMapped.lean` |
| [Definition 3.15, p. 25](../binary-field-counterexamples.pdf#page=25). Quadratic Boolean functions and polar forms | `BinaryQuadraticData`, `polarMap`, `radical`; `tensorPolarMap`, `tensorPolarRank` | `Constructions/Gold/QuadraticCharacters.lean`; `Constructions/Gold/Polar.lean` |
| [Definition 3.17, p. 26](../binary-field-counterexamples.pdf#page=26). Locator padding | No separate declaration. Padding is multiplication by the locator; its properties are `padding_witness_degree`, `agreementCount_padding_union`, `nonzeroBadChallenges_padding` | `Constructions/Gold/PaddingPolynomials.lean` |
| [Definition 5.7, p. 41](../binary-field-counterexamples.pdf#page=41). Gold moments | `goldMoment` | `Constructions/Gold/Moments.lean` |
| [Definition 5.20, p. 51](../binary-field-counterexamples.pdf#page=51). Quadratic forms, radicals, and rank | Mathlib `QuadraticForm` and `QuadraticMap.radical`; the rank is the codimension of the radical, as in `traceRankFamily`. Elliptic type: `IsElliptic` | `Constructions/QuadraticForms/TraceRadicalIncidence.lean`; `Constructions/QuadraticForms/EllipticType.lean` |
| [Definition 6.2, p. 59](../binary-field-counterexamples.pdf#page=59). Translation periods and essential coordinates | `IsPeriod`; `periodSubmodule`; `essentialDualSpace`, `essentialDimension` | `Constructions/Trees/Templates.lean`; `Constructions/Trees/BranchRecovery.lean`; `Constructions/Trees/Intrinsic/Essential.lean` |
| [Definition 6.3, p. 59](../binary-field-counterexamples.pdf#page=59). Tree functions | `IsHeightTwoTree`, `IsTreeFunction`; `IsTreeRoot` | `Constructions/Trees/Intrinsic/Definition.lean`; `Constructions/Trees/Intrinsic/RootData.lean` |
| [Definition 6.8, p. 62](../binary-field-counterexamples.pdf#page=62). Tree functions avoiding a subspace | `IsAvoidingTree` | `Constructions/Trees/Intrinsic/Avoiding.lean` |

### Remarks, unnumbered claims and numerical bounds

| Paper location and claim | Lean declarations | File |
|---|---|---|
| Abstract. Length above 2^20 excludes 90 bits over a 128-bit field | `quadratic_above_length20_probability` | `MainTheorems/FrontMatterProbability.lean` |
| Abstract and Section 1. Rate 1/4: common agreement 25%, Johnson 50% | `prose_quarter_rate_percentages` | `MainTheorems/ProseArithmetic.lean` |
| Abstract and Section 1. Tree agreement 17/32 is 53.125% | `prose_tree_agreement_percentage` | `MainTheorems/ProseArithmetic.lean` |
| Abstract and Section 1. Superpolynomial decoding lists on dense domains at a fixed agreement, and the resulting bound on explicit list output | `fixed_agreement_dense_ordinary_list_obstruction`, `fixed_agreement_dense_explicit_output_step_obstruction` | `MainTheorems/FixedAgreementListObstruction.lean` |
| Section 1. Full-field rates 4^-k: lists at a fixed agreement and explicit list output | `full_field_fixed_agreement_ordinary_list_obstruction`, `full_field_fixed_agreement_explicit_output_step_obstruction` | `MainTheorems/FullFieldFixedAgreementLists.lean` |
| Section 1. The unit group of a binary field has odd order, so it has no nontrivial subgroup of power-of-two size | `prose_binary_unit_group_odd`, `prose_binary_multiplicative_subgroup_power_two_trivial` | `Arithmetic/BinaryMultiplicativeDomains.lean` |
| Section 1. Domain densities 1/32 (V_27) and 2^-42 (LeanVM) | `prose_native27_domain_density`, `prose_leanvm_domain_density` | `MainTheorems/ProseArithmetic.lean` |
| Section 1. Johnson agreement 25% at rate 1/16 | `prose_sixteenth_rate_johnson_percentage` | `MainTheorems/ProseArithmetic.lean` |
| Section 4.2. Rate 1/8 with 22 queries: (√(1/8))^22 = 2^-33, the shortfall from 60 bits, and the 15.1% threshold | `prose_johnson_eighth_queries`, `prose_query_johnson_sixty_bit_shortfall`, `prose_sixty_bit_query_threshold_percentage`, `prose_sixty_bit_query_target_iff` | `MainTheorems/ProseArithmetic.lean` |
| Section 1. More than 2^64 exceptions are required over a 192-bit field; the quadratic count at N = 2^22 is below 2^42 | `prose_192_bit_exception_requirement`, `prose_quadratic_length22_actual_count` | `MainTheorems/ProseArithmetic.lean` |
| Section 1. Tree bounds fall short of the targets by more than 100 bits; Johnson 70.71% at rate 1/2 | `prose_tree_bit_shortfalls`, `prose_half_rate_johnson_percentage` | `MainTheorems/ProseArithmetic.lean` |
| Section 1. Full-field Johnson deficit in coordinates and as a fraction | `introduction_full_field_johnson_deficit` | `MainTheorems/DiscussionConsequences.lean` |
| Section 1. A field of size at least M keeps more than M/2 challenges | `quadratic_near_johnson_more_than_half_population` | `MainTheorems/QuadraticPopulationBound.lean` |
| Section 1. N = 2^20, q = 2^128: probability above 2^-90.585 | `quadratic_length20_probability` | `MainTheorems/FrontMatterProbability.lean` |
| Section 4.2. Two repetitions at rate 1/8: probability above 2^-57.17 | `rate_eighth_two_repetitions_product_probability` | `MainTheorems/FrontMatterProbability.lean` |
| Table 1. N = 2^22, q = 2^128: probability above 2^-87 | `quadratic_length22_probability` | `MainTheorems/FrontMatterProbability.lean` |
| Section 3.1. Minimum distances as attained minima; no common witness at the target agreement | `prose_individual_distance_isLeast`, `prose_interleaved_distance_isLeast`, `prose_no_common_target_witness` | `Agreement/ProseConsequences.lean` |
| Section 3.1. Common-agreement gap: distance of the combination, proximity loss, and the one-coordinate gap | `prose_combination_distance_le_target`, `prose_proximity_loss_exceeded`, `prose_single_coordinate_gap_vanishes` | `Agreement/ProseConsequences.lean` |
| Section 3.1. Reduction to the canonical representative can change values in an extension field | `prose_canonical_reduction_changes_extension_value` | `Agreement/ProseConsequences.lean` |
| Section 3.1. Distinct polynomials of degree below K give distinct codewords | `strictDegree_evaluation_injective`, `strictDegree_codeword_image_card` | `Polynomial/SectionThreeCanonical.lean` |
| Definition 3.6. Uniqueness of the canonical representative and its description as a remainder | `existsUnique_canonicalRepresentative`, `canonicalRepresentative_eq_remainder`, `canonicalRepresentative_univ_eq_remainder` | `Polynomial/SectionThreeCanonical.lean` |
| Section 3.1. Gaussian coefficient bounds and the infinite product below 4 | `gaussianBinomial_sharp_bounds`; `gaussian_inverse_infiniteProduct_lt_four` | `Counting/GaussianSharpBound.lean`; `Counting/GaussianInfiniteProduct.lean` |
| Section 3.1. Lower bound on each Gaussian factor and the logarithmic estimate with bounded error | `prose_gaussian_product_factor_lower`, `prose_gaussian_logarithm_error` | `Counting/ProseLogarithms.lean` |
| Section 3.1. Dimension-removal formula and the binary values for dimensions 1, 2, 3 | `gaussianBinomial_dimension_ratio`, `gaussianBinomial_binary_one`, `gaussianBinomial_binary_two`, `gaussianBinomial_binary_three` | `Counting/SectionThreeCompanions.lean` |
| Section 3.2. Binary linearized polynomials and subspace locators are additive | `IsBinaryLinearized.isAdditivePolynomial`, `subspacePolynomial_isAdditivePolynomial` | `Polynomial/SectionThreeAdditivity.lean` |
| Section 3.2. An affine-flat locator plus cX is a square | `affineFlatLocator_square_full` | `Polynomial/SectionThreeAdditivity.lean` |
| Section 3.3. Root-count remark before Lemma 3.13 | `primePowerLocatorRoot_agreementCount_le` | `Constructions/QuadraticForms/AffineQuarterSource.lean` |
| Section 3.4. Locator formula after Lemma 3.16, its converse, and the twice-degree characterization | `booleanLocator_forward_full`, `booleanLocator_converse_full`, `booleanLocator_exact_agreement_iff` | `Constructions/NearUnit/BooleanLocatorConverse.lean` |
| Section 3.4. Every affine subspace of positive dimension is such a set | `booleanLocator_affine_exact_agreement`, `booleanLocator_singleton_not_twice_degree` | `Constructions/NearUnit/BooleanLocatorConverse.lean` |
| Section 4.1. The count holds at the largest integer below the Johnson threshold | `quadratic_near_johnson_at_largest_below_johnson` | `MainTheorems/QuadraticNearJohnsonFull.lean` |
| Section 4.1. Decoding lists at rate 1/8 | `quadratic_near_johnson_exact_with_decoding_list` | `MainTheorems/QuadraticNearJohnsonFull.lean` |
| Section 4.2. Number of codimension-s subspaces is Θ_s(N^s) | `binary_codimension_subspaces_count_and_bounds`, `binary_codimension_subspaces_isTheta` | `Constructions/AllRates/SubspaceAsymptotics.lean` |
| Section 4.2. Polynomial and quadratic counts after Theorem 4.5 | `all_rates_certain_failure_polynomial_count`, `all_rates_certain_failure_quadratic_count` | `MainTheorems/AllRatesPolynomialCount.lean` |
| Section 4.2. If zero is an exceptional challenge, the first input is close | `prose_all_challenges_first_input_close` | `Agreement/ProseConsequences.lean` |
| Section 4.3. Exceptional probability exactly 1 − 1/N | `exact_half_agreement_full` | `MainTheorems/ExactHalfAgreementProbability.lean` |
| Section 5.1. A field of dimension at least 2d is outside the parameter range | `delta_signed_lt_one_of_double_dimension` | `Constructions/Gold/ParameterRemarks.lean` |
| Section 5.1. LeanVM and Flock parameter arithmetic | `leanVM_delta_lt_one`, `flock_delta_lt_one` | `Constructions/Gold/ParameterRemarks.lean` |
| Section 5.1. A subfield containing a domain that contains a field generator is the whole field | `containing_generator_subfield_eq_top` | `Constructions/Gold/ParameterRemarks.lean` |
| Section 5.2. Logarithmic expansion in the proof of Corollary 5.3, with explicit error bound | `gold_full_field_fixed_extension_log_expansion`, `gold_full_field_fixed_extension_log_error` | `MainTheorems/FixedExtensionExpansion.lean` |
| Section 5.3. Full-field example after Lemma 5.5; the label space can differ from the domain | `parameterPolynomial_full_field`, `exists_domain_ne_parameterDomain` | `Constructions/Gold/FullFieldLabels.lean` |
| Section 5.3. Every quadratic function vanishing at 0 has exactly one representation | `existsUnique_quadratic_gold_representation` | `Constructions/Gold/QuadraticRepresentation.lean` |
| Remark 5.11. Rank, moments, and degree for arbitrary rank | `repairedPolynomial_general_rank_degree`, `tensorLinearPart_general_rank_degree` | `Constructions/Gold/RankDegreeFull.lean` |
| Section 5.3. Locator of the level set as a square plus a multiple of X | `repairedLocator_levelLocator_eq` | `Constructions/Gold/LevelLocator.lean` |
| Section 5.3. Rank-two paragraph | `rankTwo_subspace_locators_full`, `rankTwo_vanishing_radical_smaller_level_coset` | `Constructions/Gold/RankTwo.lean` |
| Section 5.6. Retention probability tends to 1 | `paddingRetentionProbability_half_rate_tendsto`, `denseGold_paddingRetentionProbability_tendsto` | `Constructions/Gold/RetentionLimit.lean` |
| Section 5.6. 5/8 is below the Johnson fraction at rate 1/2 | `half_rate_limit_lt_johnson` | `Constructions/Gold/ParameterRemarks.lean` |
| Section 5.7. Binius prefix domains: V_32 is the subfield of size 2^32, and smaller prefixes lie in it | `biniusPrefixDomain_thirtytwo_eq_fixed`, `biniusPrefixDomain_le_fixed_thirtytwo` | `Constructions/Gold/BiniusBasis.lean` |
| Section 5.7. The full 128-bit field is outside the range of Theorem 5.1 for these domains | `binius_fullfield_gold_min_dimension` | `Constructions/Gold/BiniusBasis.lean` |
| Section 5.7. Decoding list over the 32-bit field before padding | `native32_ordinary_list` | `MainTheorems/Native32List.lean` |
| Section 5.7. Retention probability and probability exponent of Corollary 5.18, to the printed digits | `native128_retention_decimal`, `native128_probability_exponent_decimal` | `MainTheorems/ApplicationDecimals.lean` |
| Section 5.7. 0.58 and 24.42 percentage points | `native128_percentage_gaps` | `MainTheorems/ApplicationDecimals.lean` |
| Section 5.7. Rate-1/2 Binius64 example | `halfRateBinius64` | `MainTheorems/HalfRateBinius64.lean` |
| Sections 5.1 and 5.7. Affine translates by arbitrary elements of the challenge field | `nonzeroBadChallenges_translatedWord`, `ordinaryList_translatedDomain`; `gold_counting_sharp_affine_translate`, `native128Example_sharp_affine_translate`, `halfRateBinius64_affine_translate` | `Agreement/DomainTranslation.lean`; `MainTheorems/AffineTranslateExamples.lean` |
| Section 5.8. Longfellow specification domain: injection, cardinality, central affine 11-space, non-affineness, rate at most 1/7 | `longfellow_specification_power_basis`; `bitInjection`, `inj_eq_bitInjection`, `inj_eq_power_sum`, `lowSpace_eq_span`; `central_interval_eq` | `MainTheorems/LongfellowSpecification.lean`; `Constructions/Longfellow/DomainCoordinates.lean`; `Constructions/Longfellow/Domain.lean` |
| Section 5.8. The injection sends every aligned block `c·2^k, …, (c+1)·2^k − 1` in the sixteen-bit range onto an affine subspace of dimension `k` | `aligned_interval_eq`, `alignedLowSpace_eq_span`, `alignedLowSpace_finrank`, `alignedLowSpace_card`, `aligned_interval_card` | `Constructions/Longfellow/AlignedBlocks.lean` |
| Section 5.8. The common agreement is the least possible | `longfellow_specification_minimal_common_agreement` | `MainTheorems/LongfellowSpecification.lean` |
| Section 5.8. Probability exponent 105.5216 | `longfellow_probability_exponent_decimal` | `MainTheorems/ApplicationDecimals.lean` |
| Section 5.8. Table 6 agreement percentages; 14.3% and 57.1%; Johnson 37.8%; about 12 percentage points | `longfellow_table_percentages`, `longfellow_common_unique_percentages`, `longfellow_johnson_percentages`, `longfellow_johnson_gap_percentages` | `MainTheorems/ApplicationDecimals.lean` |
| Section 5.9. Asymptotic pairs for every prime power; examples for b = 3 and b = 4 | `primePower_pairs_near_johnson`, `primePower_middle_rank_common_gap_tendsto`, `primePower_three_four_rate_examples` | `MainTheorems/PrimePowerPairAsymptotics.lean` |
| Section 5.9. Comparison of the binary Gold and elliptic factors | `binary_gold_elliptic_factor_comparison` | `MainTheorems/ApplicationDecimals.lean` |
| Section 5.9. For b > 2 a level set of the required size is a translate of an elliptic zero set | `affine_elliptic_level_set_is_translate` | `Constructions/QuadraticForms/AffineLevelElliptic.lean` |
| Section 6.1. Minimality of the essential dual space | `factors_through_tests_iff`, `essentialDimension_le_number_of_tests` | `Constructions/Trees/Intrinsic/Minimality.lean` |
| Section 6.2. Height two: the four-point support splits into two lines in three ways | `heightTwoMuxSupport_card`, `heightTwoMuxLinePartitions_card`, `heightTwoDecomposition_parts_are_affine_lines`, `heightTwoDecomposition_lines_not_parallel`, `heightTwoMux_coordinate_transport` | `Constructions/Trees/HeightTwoDecompositions.lean` |
| Sections 6.2 and 6.3. Collision energy at most N M^2 / 8 | `whole_tree_energy_le_eighth`, `avoiding_tree_energy_le_eighth_of_half` | `Constructions/Trees/SharpEnergy.lean` |
| Section 6.2. Cubic count at height two when q ≥ N^4 | `half_agreement_trees_height_two_cubic` | `MainTheorems/TreeGrowthCorollaries.lean` |
| Section 6.3. Height-three formula for M_3(d) and its leading constant 105/16 | `avoidingTreeSupportCount_three_closed`; `avoidingTreeSupportCount_three_limit` | `Constructions/Trees/HeightThreeFormula.lean`; `Constructions/Trees/HeightThreeLimit.lean` |
| Section 6.3. Fractional common-agreement gap 2^(-h-1) | `binary_tree_fractional_gap` | `MainTheorems/IntrinsicAvoidingTrees.lean` |
| Section 6.3. Superquadratic growth; parameters at heights 3, 4, 5 | `half_rate_decision_trees_superquadratic`, `tree_height_three_four_five_parameters` | `MainTheorems/TreeGrowthCorollaries.lean` |
| Section 6.3. Height two at agreement 5/8 | `half_rate_decision_trees_height_two_count` | `MainTheorems/TreeGrowthCorollaries.lean` |
| Section 6.3. Words over a subfield containing the domain | `half_rate_decision_trees_subfield` | `MainTheorems/TreeSubfield.lean` |
| Section 6.4. Height 3 and 4 counts and probabilities over 192-bit and 256-bit fields | `leanVM_tree_height_three`, `leanVM_tree_height_four`, `flock_tree_height_four` | `MainTheorems/TreeConcrete.lean` |
| Section 7. Rate 1/2: one pair with agreement tending to 5/8 and superpolynomially many exceptions; 0.625 and 0.707 | `discussion_half_rate_superpolynomial_limit`; `prose_discussion_half_rate_decimals` | `MainTheorems/DiscussionConsequences.lean`; `MainTheorems/ProseArithmetic.lean` |
| Section 7. Words over a subfield B: exceptional challenges lie in B, and the probability is at most the ratio of the field sizes | `native_badChallenges_subset_subfield`, `native_exceptional_probability_le_subfield` | `Agreement/SubfieldExceptionalBound.lean` |

The scripts `scripts/verify_main_parameters.py` and
`scripts/verify_fixed_extension.py` recompute the printed finite parameters
exactly, as an independent check alongside the Lean proofs.

### Scope

The following are outside the formalization.

- **Descriptions of deployed systems.** What Binius64, Longfellow, Flock and
  LeanVM implement or configure is not a Lean statement. Lean proves the
  mathematical statements about the domains and parameters as the paper
  describes them. For example, it proves the Binius prefix-domain facts for any
  basis satisfying the stated recurrence, and the Longfellow results for the
  domain given by powers of a generator whose first 16 powers form a basis.
  That a system uses this basis, domain or field is taken from its
  specification or source.
- **Results quoted from the literature for comparison.** Prior bounds,
  security estimates of the systems, and comparisons with other papers are not
  formalized.

Asymptotic statements are proved in explicit form: a constant and a size
threshold exist such that the bound holds for all larger parameters.

Five Lean statements carry a condition that should be read together with the
paper's sentence.

- **Pole reduction (Lemma 3.11).** `normalizedPoleReduction_full` is for a
  nonempty index set. The paper states the same condition.
- **Subfield bound (Section 7).** `native_exceptional_probability_le_subfield`
  requires the agreement threshold to exceed the common agreement of the pair.
  The paper states the same condition.
- **Probability above 2^-90.585 (Section 1).** `quadratic_length20_probability`
  assumes a challenge field of size 2^128. The paper states this field size.
- **Affine subspaces (Section 3.4).** `booleanLocator_affine_exact_agreement`
  is for affine subspaces of positive dimension, and
  `booleanLocator_singleton_not_twice_degree` shows that a single point is
  excluded. The paper states the claim for positive dimension.
- **Smallest containing field (Section 5.1).**
  `containing_generator_subfield_eq_top` assumes that the domain contains an
  element generating the field. That the LeanVM and Flock domains contain such
  an element is part of the description of those systems.

## Validation

After `lake build`, run from the repository root:

```sh
python3 scripts/check_lean_contract_axioms.py
```

It elaborates [Checks/Axioms.lean](Checks/Axioms.lean) and
[Checks/StatementTypes.lean](Checks/StatementTypes.lean), requires their
`#print axioms` inventory to match every public declaration in the source
tree, and rejects any axiom outside the standard three.
