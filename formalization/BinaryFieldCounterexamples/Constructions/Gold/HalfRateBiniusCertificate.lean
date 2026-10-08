/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Native128Certificate

/-!
# Exact numerical certificate for half-rate Binius64 parameters

The Binius64 application of Corollary 5.15 uses `m = 32`, `d = 27`,
`t = 6`, padding dimension `25`, and `q = 2^128`. The retained bound is
the ceiling of the exact retention probability times both collision bounds.
We evaluate it over the rationals, then certify its thousandth power over
the integers to prove the real probability comparison. All proofs are kernel
checked and use only standard axioms.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Exact retained lower bound at padding dimension 25 (rate one half). -/
noncomputable def halfRateBiniusCount : ℕ :=
  ⌈paddingRetentionProbability 27 25 12 * nativeGoldPoleCountSharp⌉₊

/-- Exact retained bound, not the full exceptional-set size. -/
theorem halfRateBiniusCount_value :
    halfRateBiniusCount = 345129489779595974011716533694 := by
  rw [halfRateBiniusCount, nativeGoldPoleCountSharp_value,
    paddingRetentionProbability_product 27 25 12 (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]
  rw [Nat.ceil_eq_iff (by decide)]
  norm_num

/-- The paper's conservative scientific-notation count. -/
theorem halfRateBiniusCount_lower : 345123 * 10^24 < halfRateBiniusCount := by
  rw [halfRateBiniusCount_value]
  norm_num

set_option exponentiation.threshold 100000
/-- An exact integer certificate for the real-power probability comparison. -/
theorem halfRateBinius_probability_integer_certificate : (2:ℕ)^98123<(345129489779595974011716533694)^1000 := by
  norm_num
set_option exponentiation.threshold 256
/-- The conservative integer lower bound already exceeds the advertised real-power probability threshold. -/
theorem halfRateBinius_probability_lower :
    Real.rpow 2 (-(29877/1000:ℝ))<(345129489779595974011716533694:ℝ)/(2:ℝ)^128 := by
  apply (Real.rpow_lt_rpow_iff (x := Real.rpow 2 (-(29877/1000:ℝ)))
    (y := (345129489779595974011716533694:ℝ)/(2:ℝ)^128) (z := (1000:ℝ))
    (Real.rpow_nonneg (by norm_num) _) (by positivity) (by norm_num)).mp
  change Real.rpow (Real.rpow 2 (-(29877/1000:ℝ))) (1000:ℝ)<
    Real.rpow ((345129489779595974011716533694:ℝ)/(2:ℝ)^128) (1000:ℝ)
  have hleft : Real.rpow (Real.rpow 2 (-(29877/1000:ℝ))) (1000:ℝ)=((2:ℝ)^29877)⁻¹ := by
    apply (Real.rpow_mul (x := (2:ℝ)) (by norm_num) (-(29877/1000:ℝ)) (1000:ℝ)).symm.trans
    rw [show -(29877/1000:ℝ)*1000=-(29877:ℝ) by norm_num,Real.rpow_neg (by norm_num)]
    congr 1
    exact Real.rpow_natCast 2 29877
  rw [hleft]
  have hright : Real.rpow ((345129489779595974011716533694:ℝ)/(2:ℝ)^128) (1000:ℝ)=
      ((345129489779595974011716533694:ℝ)/(2:ℝ)^128)^1000 := Real.rpow_natCast _ 1000
  rw [hright,div_pow,←pow_mul]
  change ((2:ℝ)^29877)⁻¹<(345129489779595974011716533694:ℝ)^1000/(2:ℝ)^128000
  rw [←one_div,div_lt_div_iff₀ (by positivity) (by positivity),one_mul]
  have hc : (2:ℝ)^98123<(345129489779595974011716533694:ℝ)^1000 := by
    exact_mod_cast halfRateBinius_probability_integer_certificate
  have hm := mul_lt_mul_of_pos_right hc (by positivity : (0:ℝ)<2^29877)
  rw [←pow_add] at hm
  change (2:ℝ)^128000<(345129489779595974011716533694:ℝ)^1000*2^29877 at hm
  exact hm
set_option exponentiation.threshold 256

/-- Both decimal bounds for the exact retained count. -/
theorem halfRateBiniusCount_certificate :
    345123 * 10^24 < halfRateBiniusCount ∧
    Real.rpow 2 (-(29877/1000:ℝ)) < (halfRateBiniusCount:ℝ)/(2:ℝ)^128 := by
  exact ⟨halfRateBiniusCount_lower, by
    rw [halfRateBiniusCount_value]
    exact halfRateBinius_probability_lower⟩

end BinaryFieldCounterexamples.Gold
