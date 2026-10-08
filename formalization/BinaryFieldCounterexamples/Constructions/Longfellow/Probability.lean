/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
# Exact probability bound for the Longfellow list size

The exact list size `5,843,376` exceeds the claimed probability threshold
`2^(-105.522)` relative to a 128-bit challenge space. The real-power comparison
is reduced to a strict integer inequality, proved by kernel-checked `norm_num`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow

set_option exponentiation.threshold 100000
/-- Exact integer certificate for the decimal probability threshold. -/
theorem probability_integer_certificate :
    (2 : ℕ) ^ 11239 < 5843376 ^ 500 := by
  norm_num
set_option exponentiation.threshold 256

/-- The exact list size gives the claimed probability lower bound in a
128-bit challenge space. -/
theorem probability_lower_rational :
    Real.rpow 2 (-(52761 / 500 : ℝ)) <
      (5843376 : ℝ) / (2 : ℝ) ^ 128 := by
  apply (Real.rpow_lt_rpow_iff
    (x := Real.rpow 2 (-(52761 / 500 : ℝ)))
    (y := (5843376 : ℝ) / (2 : ℝ) ^ 128)
    (z := (500 : ℝ))
    (Real.rpow_nonneg (by norm_num) _)
    (by positivity)
    (by norm_num)).mp
  change Real.rpow (Real.rpow 2 (-(52761 / 500 : ℝ))) (500 : ℝ) <
    Real.rpow ((5843376 : ℝ) / (2 : ℝ) ^ 128) (500 : ℝ)
  have hleft : Real.rpow (Real.rpow 2 (-(52761 / 500 : ℝ))) (500 : ℝ) =
      ((2 : ℝ) ^ 52761)⁻¹ := by
    apply (Real.rpow_mul (x := (2 : ℝ)) (by norm_num)
      (-(52761 / 500 : ℝ)) (500 : ℝ)).symm.trans
    rw [show -(52761 / 500 : ℝ) * 500 = -(52761 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num)]
    congr 1
    exact Real.rpow_natCast 2 52761
  rw [hleft]
  have hright : Real.rpow ((5843376 : ℝ) / (2 : ℝ) ^ 128) (500 : ℝ) =
      ((5843376 : ℝ) / (2 : ℝ) ^ 128) ^ 500 := Real.rpow_natCast _ 500
  rw [hright, div_pow, ← pow_mul]
  change ((2 : ℝ) ^ 52761)⁻¹ <
    (5843376 : ℝ) ^ 500 / (2 : ℝ) ^ 64000
  rw [← one_div, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  have hc : (2 : ℝ) ^ 11239 < (5843376 : ℝ) ^ 500 := by
    exact_mod_cast probability_integer_certificate
  have hm := mul_lt_mul_of_pos_right hc (by positivity : (0 : ℝ) < 2 ^ 52761)
  rw [← pow_add] at hm
  change (2 : ℝ) ^ 64000 < (5843376 : ℝ) ^ 500 * 2 ^ 52761 at hm
  exact hm

/-- Decimal-exponent form of the probability bound used in the application. -/
theorem probability_lower :
    (2 : ℝ) ^ (-105.522 : ℝ) < (5843376 : ℝ) / (2 : ℝ) ^ 128 := by
  change Real.rpow 2 (-105.522 : ℝ) < _
  rw [show (-105.522 : ℝ) = -(52761 / 500 : ℝ) by norm_num]
  exact probability_lower_rational

end BinaryFieldCounterexamples.Longfellow
