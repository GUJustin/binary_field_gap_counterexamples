/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact certificates for the concrete half-rate tree examples

Section 6.4 substitutes dimension 22 and heights 3 and 4 into
Theorem 6.10. These certificates evaluate its rational incidence energy and
both terms of its collision bound, without replacing that energy by a coarser
bound. Decimal claims are conservative exact comparisons, and the fractional
power claim follows from a kernel-checked integer certificate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees

/-- Exact rational incidence energy from Theorem 6.10, for dimension 22. -/
noncomputable def concreteTreeEnergy (h : ℕ) : ℚ :=
  let N : ℕ := 2^22
  let K : ℕ := N/2
  let w : ℕ := N/2^(h+1)
  let M : ℕ := avoidingTreeSupportCount h 22
  (((K : ℚ)-w-(K : ℚ)^2/(N-w))*M^2+w*M)/2

/-- Both collision bounds, including the natural floor and ceiling. -/
noncomputable def concreteTreeCount (h bits : ℕ) : ℕ :=
  let M := avoidingTreeSupportCount h 22
  let E := concreteTreeEnergy h
  max (M-⌊E/((2:ℚ)^bits-2^22)⌋₊)
    ⌈((2:ℚ)^bits-2^22)*(M:ℚ)^2/(((2:ℚ)^bits-2^22)*M+2*E)⌉₊

/-- The exact number of height-three supports. -/
theorem concreteTreeSupportCount_three :
    avoidingTreeSupportCount 3 22 = 2030934687750743930807500800 := by
  norm_num [avoidingTreeSupportCount, gaussianBinomial, treeSupportCount,
    treeDenominator, Finset.prod_range_succ]

/-- The exact number of height-four supports. -/
theorem concreteTreeSupportCount_four :
    avoidingTreeSupportCount 4 22 =
      1209318576099013638293336448850522895725736998921768883135101009920000 := by
  norm_num [avoidingTreeSupportCount, gaussianBinomial, treeSupportCount,
    treeDenominator, Finset.prod_range_succ]

/-- The exact height-three incidence energy. -/
theorem concreteTreeEnergy_three : concreteTreeEnergy 3 =
    1477727782544148020093746244178417523243940369173828966809600 := by
  norm_num [concreteTreeEnergy, concreteTreeSupportCount_three]

/-- The exact height-four incidence energy. -/
theorem concreteTreeEnergy_four : concreteTreeEnergy 4 =
    646168779935585404126068177774678276530026949082595543041273747923437937354754549881358575078095750787816831561287570997837401853172771717120000 := by
  norm_num [concreteTreeEnergy, concreteTreeSupportCount_four]

/-- Exact height-three count over the 192-bit challenge field. -/
theorem concreteTreeCount_three_192 : concreteTreeCount 3 192 =
    2030934687750743930807500565 := by
  have hf : ⌊concreteTreeEnergy 3/((2:ℚ)^192-2^22)⌋₊ = 235 := by
    rw [Nat.floor_eq_iff (by norm_num [concreteTreeEnergy_three, concreteTreeEnergy_four])]
    norm_num [concreteTreeEnergy_three]
  have hc : ⌈((2:ℚ)^192-2^22)*(avoidingTreeSupportCount 3 22:ℚ)^2/
      (((2:ℚ)^192-2^22)*(avoidingTreeSupportCount 3 22)+2*concreteTreeEnergy 3)⌉₊ = 2030934687750743930807500330 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num [concreteTreeSupportCount_three, concreteTreeEnergy_three]
  unfold concreteTreeCount
  dsimp only
  rw [hf, hc]
  norm_num [concreteTreeSupportCount_three]

/-- Exact height-four count over the 192-bit challenge field. -/
theorem concreteTreeCount_four_192 : concreteTreeCount 4 192 =
    7103373469922630731168802544744297143231762030400873 := by
  have hf : ⌊concreteTreeEnergy 4/((2:ℚ)^192-2^22)⌋₊ = 102940625654170673461034704974142960983041966246398916506763024417778626860456767437727 := by
    rw [Nat.floor_eq_iff (by norm_num [concreteTreeEnergy_three, concreteTreeEnergy_four])]
    norm_num [concreteTreeEnergy_four]
  have hc : ⌈((2:ℚ)^192-2^22)*(avoidingTreeSupportCount 4 22:ℚ)^2/
      (((2:ℚ)^192-2^22)*(avoidingTreeSupportCount 4 22)+2*concreteTreeEnergy 4)⌉₊ = 7103373469922630731168802544744297143231762030400873 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num [concreteTreeSupportCount_four, concreteTreeEnergy_four]
  unfold concreteTreeCount
  dsimp only
  rw [hf, hc]
  norm_num [concreteTreeSupportCount_four]

/-- Exact height-four count over the 256-bit challenge field. -/
theorem concreteTreeCount_four_256 : concreteTreeCount 4 256 =
    1203738153600450193532348559198379334481679302144198224930361796779254 := by
  have hf : ⌊concreteTreeEnergy 4/((2:ℚ)^256-2^22)⌋₊ = 5580422498563444760987889652143561244057696777570658204739213140746 := by
    rw [Nat.floor_eq_iff (by norm_num [concreteTreeEnergy_three, concreteTreeEnergy_four])]
    norm_num [concreteTreeEnergy_four]
  have hc : ⌈((2:ℚ)^256-2^22)*(avoidingTreeSupportCount 4 22:ℚ)^2/
      (((2:ℚ)^256-2^22)*(avoidingTreeSupportCount 4 22)+2*concreteTreeEnergy 4)⌉₊ = 1198259793012064650929260064227095270397983510047142258516825913017923 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num [concreteTreeSupportCount_four, concreteTreeEnergy_four]
  unfold concreteTreeCount
  dsimp only
  rw [hf, hc]
  norm_num [concreteTreeSupportCount_four]

/-- The conservative decimal bound printed for LeanVM height three. -/
theorem concreteTreeCount_three_decimal :
    20309*10^23 < concreteTreeCount 3 192 := by
  rw [concreteTreeCount_three_192]
  norm_num

/-- The dyadic count bound printed for LeanVM height four. -/
theorem concreteTreeCount_four_192_lower :
    2^172 < concreteTreeCount 4 192 := by
  rw [concreteTreeCount_four_192]
  norm_num

/-- The dyadic count bound printed for Flock height four. -/
theorem concreteTreeCount_four_256_lower :
    2^229 < concreteTreeCount 4 256 := by
  rw [concreteTreeCount_four_256]
  norm_num

/-- The paper's direct first-term certificate for Flock. -/
theorem concreteTreeCount_four_256_first_term :
    ((2:ℚ)^256-2^22)*((avoidingTreeSupportCount 4 22:ℚ)-2^229-1) >
      concreteTreeEnergy 4 := by
  norm_num [concreteTreeSupportCount_four, concreteTreeEnergy_four]

set_option exponentiation.threshold 100000

/-- Raising to the positive 500th power certifies the decimal probability
exponent without trusting an approximate logarithm. -/
theorem concreteTree_probability_integer_certificate :
    (2:ℕ)^45357 < (20309*10^23)^500 := by
  norm_num

/-- The height-three decimal count lower bound already exceeds the claimed
probability threshold over a 192-bit challenge field. -/
theorem concreteTree_probability_lower :
    Real.rpow 2 (-(101286/1000:ℝ)) < (20309*10^23:ℝ)/(2:ℝ)^192 := by
  apply (Real.rpow_lt_rpow_iff (x := Real.rpow 2 (-(101286/1000:ℝ)))
    (y := (20309*10^23:ℝ)/(2:ℝ)^192) (z := (500:ℝ))
    (Real.rpow_nonneg (by norm_num) _) (by positivity) (by norm_num)).mp
  change Real.rpow (Real.rpow 2 (-(101286/1000:ℝ))) (500:ℝ) <
    Real.rpow ((20309*10^23:ℝ)/(2:ℝ)^192) (500:ℝ)
  have hl : Real.rpow (Real.rpow 2 (-(101286/1000:ℝ))) (500:ℝ) =
      ((2:ℝ)^50643)⁻¹ := by
    apply (Real.rpow_mul (x := (2:ℝ)) (by norm_num)
      (-(101286/1000:ℝ)) (500:ℝ)).symm.trans
    rw [show -(101286/1000:ℝ)*500 = -(50643:ℝ) by norm_num,
      Real.rpow_neg (by norm_num)]
    congr 1
    exact Real.rpow_natCast 2 50643
  rw [hl]
  have hr : Real.rpow ((20309*10^23:ℝ)/(2:ℝ)^192) (500:ℝ) =
      ((20309*10^23:ℝ)/(2:ℝ)^192)^500 := Real.rpow_natCast _ 500
  rw [hr, div_pow, ← pow_mul]
  change ((2:ℝ)^50643)⁻¹ < (20309*10^23:ℝ)^500/(2:ℝ)^96000
  rw [← one_div, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  have hc : (2:ℝ)^45357 < (20309*10^23:ℝ)^500 := by
    exact_mod_cast concreteTree_probability_integer_certificate
  have hm := mul_lt_mul_of_pos_right hc (by positivity : (0:ℝ)<2^50643)
  rw [← pow_add] at hm
  exact hm

/-- Exact integer certificate that the height-four support count rounds to
`2^229.5` at one decimal place in its exponent. -/
theorem concreteTreeSupportCount_four_rounding_certificate :
    (2:ℕ)^4589 < (avoidingTreeSupportCount 4 22)^20 ∧
      (avoidingTreeSupportCount 4 22)^20 < (2:ℕ)^4591 := by
  norm_num [concreteTreeSupportCount_four]

/-- A precise meaning of the paper's support-count approximation: the binary
exponent lies strictly between 229.45 and 229.55. -/
theorem concreteTreeSupportCount_four_rounding :
    Real.rpow 2 (22945/100:ℝ) < (avoidingTreeSupportCount 4 22:ℝ) ∧
      (avoidingTreeSupportCount 4 22:ℝ) < Real.rpow 2 (22955/100:ℝ) := by
  have hp (a : ℝ) :
      Real.rpow (Real.rpow 2 a) (20:ℝ) = Real.rpow 2 (a*20) :=
    (Real.rpow_mul (by norm_num : (0:ℝ)≤2) a 20).symm
  have hm : Real.rpow (avoidingTreeSupportCount 4 22:ℝ) (20:ℝ) =
      (avoidingTreeSupportCount 4 22:ℝ)^20 := Real.rpow_natCast _ 20
  have hlow : Real.rpow (Real.rpow 2 (22945/100:ℝ)) (20:ℝ) = (2:ℝ)^4589 := by
    rw [hp, show (22945/100:ℝ)*20=(4589:ℝ) by norm_num]
    exact Real.rpow_natCast _ 4589
  have hupp : Real.rpow (Real.rpow 2 (22955/100:ℝ)) (20:ℝ) = (2:ℝ)^4591 := by
    rw [hp, show (22955/100:ℝ)*20=(4591:ℝ) by norm_num]
    exact Real.rpow_natCast _ 4591
  constructor
  · apply (Real.rpow_lt_rpow_iff
      (Real.rpow_nonneg (by norm_num) _) (by positivity) (by norm_num : (0:ℝ)<20)).mp
    change Real.rpow (Real.rpow 2 (22945/100:ℝ)) (20:ℝ) <
      Real.rpow (avoidingTreeSupportCount 4 22:ℝ) (20:ℝ)
    rw [hlow, hm]
    exact_mod_cast concreteTreeSupportCount_four_rounding_certificate.1
  · apply (Real.rpow_lt_rpow_iff
      (by positivity) (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0:ℝ)<20)).mp
    change Real.rpow (avoidingTreeSupportCount 4 22:ℝ) (20:ℝ) <
      Real.rpow (Real.rpow 2 (22955/100:ℝ)) (20:ℝ)
    rw [hm, hupp]
    exact_mod_cast concreteTreeSupportCount_four_rounding_certificate.2

/-- The coefficient of `N M²` in the second-moment denominator rounds to
0.21, explaining the paper's `q/(0.21N)` description. -/
theorem concreteTreeEnergy_four_coefficient_rounding :
    (205/1000:ℚ) < 2*concreteTreeEnergy 4 /
      ((2:ℚ)^22*(avoidingTreeSupportCount 4 22:ℚ)^2) ∧
    2*concreteTreeEnergy 4 /
      ((2:ℚ)^22*(avoidingTreeSupportCount 4 22:ℚ)^2) < (215/1000:ℚ) := by
  norm_num [concreteTreeEnergy_four, concreteTreeSupportCount_four]

/-- The guaranteed height-four LeanVM probability, multiplied by `N`,
rounds to 4.7 at one decimal place. This concerns the certified lower bound,
not an upper bound on the actual pair's exceptional probability. -/
theorem concreteTreeProbability_four_192_rounding :
    (465/100:ℚ) < (concreteTreeCount 4 192:ℚ)*(2:ℚ)^22/(2:ℚ)^192 ∧
      (concreteTreeCount 4 192:ℚ)*(2:ℚ)^22/(2:ℚ)^192 < (475/100:ℚ) := by
  norm_num [concreteTreeCount_four_192]

/-- In the Flock regime the certified count retains more than 99 percent of
all counted supports and never exceeds the support population. -/
theorem concreteTreeProbability_four_256_relative :
    (99/100:ℚ)*(avoidingTreeSupportCount 4 22:ℚ) < (concreteTreeCount 4 256:ℚ) ∧
      concreteTreeCount 4 256 ≤ avoidingTreeSupportCount 4 22 := by
  norm_num [concreteTreeCount_four_256, concreteTreeSupportCount_four]

/-- The height-four asymptotic comparison scale at dimension 22 is `2^242`. -/
theorem concreteTree_four_asymptotic_scale : ((2:ℕ)^22)^11 = 2^242 := by
  norm_num

end BinaryFieldCounterexamples.Trees
