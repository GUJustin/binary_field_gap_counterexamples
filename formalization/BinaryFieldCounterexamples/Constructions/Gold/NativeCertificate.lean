/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianBinomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
# Exact numerical certificate for the native 128-bit example

The committed Gaussian product quotient and both rational ceilings are evaluated
exactly. The resulting retained count is checked against the conservative integer
threshold. For the real-power probability claim, taking positive thousandth
powers reduces the comparison to an exact integer inequality; no logarithm or
decimal approximation is trusted.

Only the integer certificate temporarily raises the exponentiation evaluator's
threshold. Its proof uses kernel-checked `norm_num`, not native evaluation axioms.
These numerical facts are independent of the existence construction and do not
by themselves assert that any pair realizes the count.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
/-- Exact locator family size in the native 128-bit example. -/
noncomputable def nativeGoldListSize : ℕ := 2^12*3*gaussianBinomial 4 13 6
/-- The exact nonzero pole-challenge lower bound in the native example. -/
noncomputable def nativeGoldPoleCount : ℕ :=
  ⌈(nativeGoldListSize:ℚ)*((2:ℚ)^128-2^27)/((2:ℚ)^128-2^27+2^15*((nativeGoldListSize:ℚ)-1))⌉₊-1
/-- The exact padding-retained lower bound in the native example. -/
noncomputable def nativeGoldPaddedCount : ℕ :=
  ⌈(1-(((2:ℚ)^12-1)*(2^8-1)/(2^27-1)))*(nativeGoldPoleCount:ℚ)⌉₊
/-- Exact finite Gaussian quotient evaluation for the native example. -/
theorem nativeGoldListSize_value : nativeGoldListSize=345166818251997829058040360960 := by
  norm_num [nativeGoldListSize,gaussianBinomial,Finset.prod_range_succ]
/-- Exact exterior-pole ceiling, including removal of the zero challenge. -/
theorem nativeGoldPoleCount_value : nativeGoldPoleCount=345155345855890900396982497704 := by
  norm_num [nativeGoldPoleCount,nativeGoldListSize_value]
  rw [Nat.ceil_eq_iff (by decide)]
  norm_num
/-- Exact padding ceiling in the native example. -/
theorem nativeGoldPaddedCount_value : nativeGoldPaddedCount=342470008761586154232811210191 := by
  norm_num [nativeGoldPaddedCount,nativeGoldPoleCount_value]
  rw [Nat.ceil_eq_iff (by decide)]
  norm_num
/-- The paper's conservative decimal threshold is a strict integer lower bound. -/
theorem nativeGoldPaddedCount_lower : 34247*10^25<nativeGoldPaddedCount := by
  rw [nativeGoldPaddedCount_value]
  norm_num
set_option exponentiation.threshold 100000
/-- An exact integer certificate for the real-power probability comparison. -/
theorem nativeGold_probability_integer_certificate : (2:ℕ)^98111<(34247*10^25)^1000 := by
  norm_num
set_option exponentiation.threshold 256
/-- The conservative integer lower bound already exceeds the advertised real-power probability threshold. -/
theorem nativeGold_probability_lower :
    Real.rpow 2 (-(29889/1000:ℝ))<(34247*10^25:ℝ)/(2:ℝ)^128 := by
  apply (Real.rpow_lt_rpow_iff (x := Real.rpow 2 (-(29889/1000:ℝ)))
    (y := (34247*10^25:ℝ)/(2:ℝ)^128) (z := (1000:ℝ))
    (Real.rpow_nonneg (by norm_num) _) (by positivity) (by norm_num)).mp
  change Real.rpow (Real.rpow 2 (-(29889/1000:ℝ))) (1000:ℝ)<
    Real.rpow ((34247*10^25:ℝ)/(2:ℝ)^128) (1000:ℝ)
  have hleft : Real.rpow (Real.rpow 2 (-(29889/1000:ℝ))) (1000:ℝ)=((2:ℝ)^29889)⁻¹ := by
    apply (Real.rpow_mul (x := (2:ℝ)) (by norm_num) (-(29889/1000:ℝ)) (1000:ℝ)).symm.trans
    rw [show -(29889/1000:ℝ)*1000=-(29889:ℝ) by norm_num,Real.rpow_neg (by norm_num)]
    congr 1
    exact Real.rpow_natCast 2 29889
  rw [hleft]
  have hright : Real.rpow ((34247*10^25:ℝ)/(2:ℝ)^128) (1000:ℝ)=
      ((34247*10^25:ℝ)/(2:ℝ)^128)^1000 := Real.rpow_natCast _ 1000
  rw [hright,div_pow,←pow_mul]
  change ((2:ℝ)^29889)⁻¹<(34247*10^25:ℝ)^1000/(2:ℝ)^128000
  rw [←one_div,div_lt_div_iff₀ (by positivity) (by positivity),one_mul]
  have hc : (2:ℝ)^98111<(34247*10^25:ℝ)^1000 := by
    exact_mod_cast nativeGold_probability_integer_certificate
  have hm := mul_lt_mul_of_pos_right hc (by positivity : (0:ℝ)<2^29889)
  rw [←pow_add] at hm
  change (2:ℝ)^128000<(34247*10^25:ℝ)^1000*2^29889 at hm
  exact hm
/-- The exact retained integer count satisfies both conservative claims from the native example. -/
theorem nativeGoldPaddedCount_certificate :
    34247*10^25<nativeGoldPaddedCount ∧
      Real.rpow 2 (-(29889/1000:ℝ))<(nativeGoldPaddedCount:ℝ)/(2:ℝ)^128 := by
  constructor
  · exact nativeGoldPaddedCount_lower
  · apply lt_trans nativeGold_probability_lower
    apply div_lt_div_of_pos_right _ (by positivity)
    exact_mod_cast nativeGoldPaddedCount_lower
end BinaryFieldCounterexamples.Gold
