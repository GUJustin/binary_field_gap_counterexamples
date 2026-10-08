/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum

/-!
# Exact decimal certificate for the rate `1/8` example

The final numerical clause of Corollary 4.6 (p. 34) compares the exact count
`45812722234` with `2^(64-28.585)`. Taking positive 200th powers reduces this
to the integer inequality `2^7083 < 45812722234^200`. The proof uses
kernel-checked `norm_num`; no floating-point approximation or native evaluation
axiom is needed. Construction of the actual pair is assembled separately in
`MainTheorems.RateEighthProbability`.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.RateEighth

set_option exponentiation.threshold 15000

/-- Exact integer certificate for the decimal exponent in Corollary 4.6. -/
theorem probability_integer_certificate : (2 : ℕ)^7083 < 45812722234^200 := by
  norm_num

/-- The exact count in Corollary 4.6 exceeds `2^(64-28.585)`. -/
theorem count_real_lower : (2 : ℝ)^(64 - 28.585 : ℝ) < 45812722234 := by
  apply (Real.rpow_lt_rpow_iff
    (x := (2 : ℝ)^(64 - 28.585 : ℝ)) (y := 45812722234) (z := (200 : ℝ))
    (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by norm_num)).mp
  rw [← Real.rpow_mul (by norm_num), show (64 - 28.585 : ℝ)*200 = 7083 by norm_num]
  rw [show (7083 : ℝ) = (7083 : ℕ) by norm_num,
    show (200 : ℝ) = (200 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast probability_integer_certificate

/-- The exact count divided by the entire 64-bit challenge field gives
probability strictly greater than `2^(-28.585)`. -/
theorem probability_real_lower :
    (2 : ℝ)^(-28.585 : ℝ) < 45812722234/(2 : ℝ)^64 := by
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^64)).mpr
  have hc := count_real_lower
  rw [show (64 - 28.585 : ℝ) = -28.585 + 64 by norm_num,
    Real.rpow_add (by norm_num), show (64 : ℝ) = (64 : ℕ) by norm_num,
    Real.rpow_natCast] at hc
  exact hc

end BinaryFieldCounterexamples.RateEighth
