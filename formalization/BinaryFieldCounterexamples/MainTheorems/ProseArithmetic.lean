/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonExact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Exact arithmetic for the numerical prose in Sections 1 and 4.2

These certificates address the domain densities, the quadratic exceptional
population at length `2^22`, the 22-query arithmetic, and the rounded Johnson
percentage. Domain and challenge-set statements use the actual paper semantics.
The query threshold is bracketed on both sides by rational percentages, so its
rounding to `15.1%` is certified without assuming a protocol security claim.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 100000

/-- Section 1, the LeanVM domain paragraph: a `2^22`-point additive domain
in a `2^64`-element field has density exactly `2^(-42)`. -/
theorem prose_leanvm_domain_density
    {B : Type*} [Field B] [Fintype B] (D : AddSubgroup B)
    (hD : (additiveDomain D).card = 2^22) (hB : Fintype.card B = 2^64) :
    ((additiveDomain D).card : ℝ) / (Fintype.card B : ℝ) = (2 : ℝ)^(-42 : ℝ) := by
  rw [hD, hB, Real.rpow_neg (by norm_num),
    show (42 : ℝ) = (42 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Section 1, the Binius64 domain paragraph: a `2^27`-point additive domain
occupies exactly `1/32` of its containing `2^32`-element field. -/
theorem prose_native27_domain_density
    {B : Type*} [Field B] [Fintype B] (D : AddSubgroup B)
    (hD : (additiveDomain D).card = 2^27) (hB : Fintype.card B = 2^32) :
    ((additiveDomain D).card : ℚ) / (Fintype.card B : ℚ) = 1/32 := by
  rw [hD, hB]
  norm_num

/-- Section 1, the decision-tree motivation: Theorem 4.1's exact quadratic
population at `N=2^22` is `2932028910251`, strictly below `2^42`. -/
theorem prose_quadratic_length22_count :
    ((2^22-1)*(2^22-2)/6 : ℕ) = 2932028910251 ∧
      ((2^22-1)*(2^22-2)/6 : ℕ) < 2^42 := by
  norm_num

/-- Section 1's quadratic-count comparison, for actual exceptional challenges
of the proper-extension construction on each prescribed length-`2^22` domain. -/
theorem prose_quadratic_length22_actual_count
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hproper : ¬Function.Surjective φ) (D : AddSubgroup B)
    (hD : (additiveDomain D).card = 2^22) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F,
      commonAgreementEQ E (2^18) f g (2^19-1) ∧
      (badChallenges E (2^18) f g (2^20-1)).card = 2932028910251 ∧
      (badChallenges E (2^18) f g (2^20-1)).card < 2^42 := by
  obtain ⟨f, g, I, hc, _, _, hcount, _, hthreshold, _, _⟩ :=
    quadratic_near_johnson_exact φ hproper D (2^18) (by norm_num)
      ⟨18, rfl⟩ (by simpa using hD)
  have he := hthreshold (2^20-1) (by norm_num) (by norm_num)
  norm_num at hc hcount
  refine ⟨f, g, hc, ?_, ?_⟩
  · rw [he, hcount]
  · rw [he, hcount]
    norm_num

/-- Section 4.2's 22-query example: the rate-`1/8` Johnson agreement raised
to the twenty-second power is exactly `2^(-33)`. -/
theorem prose_johnson_eighth_queries :
    (Real.sqrt (1/8 : ℝ))^22 = (2 : ℝ)^(-33 : ℝ) := by
  rw [show (22 : ℕ) = 2*11 by norm_num, pow_mul,
    Real.sq_sqrt (by norm_num), Real.rpow_neg (by norm_num),
    show (33 : ℝ) = (33 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Section 4.2's `60`-bit target with `22` queries: the exact agreement
threshold `2^(-60/22)` has twenty-second power exactly `2^(-60)`. -/
theorem prose_sixty_bit_query_threshold_power :
    ((2 : ℝ)^(-30/11 : ℝ))^22 = (2 : ℝ)^(-60 : ℝ) := by
  rw [← Real.rpow_natCast _ 22, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Section 4.2's `about 15.1%` agreement for a `60`-bit query term:
the exact threshold lies strictly between `15.05%` and `15.15%`. -/
theorem prose_sixty_bit_query_threshold_percentage :
    (1505/100 : ℝ) < 100*(2 : ℝ)^(-30/11 : ℝ) ∧
      100*(2 : ℝ)^(-30/11 : ℝ) < (1515/100 : ℝ) := by
  have hp := prose_sixty_bit_query_threshold_power
  have hlo : (301/2000 : ℝ)^22 < ((2 : ℝ)^(-30/11 : ℝ))^22 := by
    rw [hp, Real.rpow_neg (by norm_num),
      show (60 : ℝ) = (60 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  have hhi : ((2 : ℝ)^(-30/11 : ℝ))^22 < (303/2000 : ℝ)^22 := by
    rw [hp, Real.rpow_neg (by norm_num),
      show (60 : ℝ) = (60 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  have hl := (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 301/2000)
    (Real.rpow_nonneg (by norm_num) _) (by decide : (22 : ℕ) ≠ 0)).mp hlo
  have hu := (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ 303/2000) (by decide : (22 : ℕ) ≠ 0)).mp hhi
  constructor <;> linarith

/-- Section 4.2's `or less` clause: for nonnegative agreement, a twenty-second
power at most `2^(-60)` is equivalent to agreement at most the exact threshold. -/
theorem prose_sixty_bit_query_target_iff (δ : ℝ) (hδ : 0 ≤ δ) :
    δ^22 ≤ (2 : ℝ)^(-60 : ℝ) ↔ δ ≤ (2 : ℝ)^(-30/11 : ℝ) := by
  rw [← prose_sixty_bit_query_threshold_power]
  exact pow_le_pow_iff_left₀ hδ (Real.rpow_nonneg (by norm_num) _)
    (by decide : (22 : ℕ) ≠ 0)

/-- Section 1's half-rate Johnson agreement: `sqrt(1/2)` rounds to
`70.71%`, lying strictly between `70.705%` and `70.715%`. -/
theorem prose_half_rate_johnson_percentage :
    (70705/1000 : ℝ) < 100*Real.sqrt (1/2 : ℝ) ∧
      100*Real.sqrt (1/2 : ℝ) < (70715/1000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)
  have hn := Real.sqrt_nonneg (1/2 : ℝ)
  constructor <;> nlinarith

/-- Section 1's decision-tree motivation: in a `192`-bit challenge field,
probability greater than `2^(-128)` is equivalent to more than `2^64` distinct
exceptional challenges in the literal paper challenge set. -/
theorem prose_192_bit_exception_requirement
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K T : ℕ) (f g : D → F)
    (hF : Fintype.card F = 2^192) :
    (2 : ℝ)^(-128 : ℝ) <
      ((badChallenges D K f g T).card : ℝ)/(Fintype.card F : ℝ) ↔
      2^64 < (badChallenges D K f g T).card := by
  rw [hF, Real.rpow_neg (by norm_num),
    show (128 : ℝ) = (128 : ℕ) by norm_num, Real.rpow_natCast]
  have hpos : (0 : ℝ) < ((2^192 : ℕ) : ℝ) := by positivity
  rw [lt_div_iff₀ hpos]
  norm_num

/-- Section 1's tree agreement percentage: the height-four threshold on the
actual `2^22`-point domain is exactly `17/32`, or `53.125%`. -/
theorem prose_tree_agreement_percentage
    {F : Type*} [Field F] [Fintype F] (D : AddSubgroup F)
    (hD : (additiveDomain D).card = 2^22) :
    100*(2228224 : ℚ)/(additiveDomain D).card = 53125/1000 := by
  rw [hD]
  norm_num

/-- Abstract and Section 1's quarter-rate percentages: on the actual domain,
message length one quarter of its cardinality is `25%`, and its asymptotic
Johnson agreement is exactly `50%`. -/
theorem prose_quarter_rate_percentages
    {F : Type*} [Field F] [Fintype F] (D : AddSubgroup F) (K : ℕ)
    (hK : 0 < K) (hD : (additiveDomain D).card = 4*K) :
    100*(K : ℚ)/(additiveDomain D).card = 25 ∧
      100*Real.sqrt ((K : ℝ)/(additiveDomain D).card) = 50 := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hKq : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  have hr : (K : ℝ)/(additiveDomain D).card = 1/4 := by
    rw [hD]
    push_cast
    field_simp
  constructor
  · rw [hD]
    push_cast
    field_simp
    norm_num
  · rw [hr]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/4)
    have hn := Real.sqrt_nonneg (1/4 : ℝ)
    nlinarith

/-- Section 4.2's 22-query comparison: the Johnson query term is strictly
larger than the `60`-bit target and has only `33` bits, a `27`-bit deficit. -/
theorem prose_query_johnson_sixty_bit_shortfall :
    (2 : ℝ)^(-60 : ℝ) < (Real.sqrt (1/8 : ℝ))^22 ∧
      (60 - 33 : ℕ) = 27 := by
  rw [prose_johnson_eighth_queries]
  constructor
  · rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      show (60 : ℝ) = (60 : ℕ) by norm_num,
      show (33 : ℝ) = (33 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
    norm_num
  · norm_num


/-- Introduction, line 198: the limiting Johnson fraction at rate `1/16`
is exactly `25%`, as opposed to its smaller finite-coordinate threshold. -/
theorem prose_sixteenth_rate_johnson_percentage :
    100 * Real.sqrt (1/16 : ℝ) = 25 := by
  have h : Real.sqrt (1/16 : ℝ) = 1/4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 1/4)]
    norm_num
  rw [h]
  norm_num

/-- Introduction, lines 285--286: the soundness ceilings `20` and `27`
are respectively `108` and `101` bits below the stated `128`-bit target. -/
theorem prose_tree_bit_shortfalls :
    (128 - 20 : ℕ) = 108 ∧ (128 - 27 : ℕ) = 101 ∧
      100 < (128 - 20 : ℕ) ∧ 100 < (128 - 27 : ℕ) := by
  norm_num

/-- Discussion, lines 24--25: `5/8` is exactly `0.625`, while the half-rate
limiting Johnson fraction `1/√2` rounds to `0.707` to three decimal places. -/
theorem prose_discussion_half_rate_decimals :
    (5/8 : ℝ) = 625/1000 ∧
      (7065/10000 : ℝ) < 1/Real.sqrt 2 ∧ 1/Real.sqrt 2 < (7075/10000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  refine ⟨by norm_num, ?_, ?_⟩
  · apply (lt_div_iff₀ hp).mpr
    nlinarith
  · apply (div_lt_iff₀ hp).mpr
    nlinarith

end BinaryFieldCounterexamples
