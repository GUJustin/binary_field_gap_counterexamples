/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianSharpBound
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 3.1: the logarithmic Gaussian coefficient estimate

The printed `log_q [a choose b]_q = b(a-b)+O(1)` follows from the
integer counting bounds with the absolute error constant two, uniformly over
all integer bases at least two and every admissible dimension.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Section 3.1, Gaussian-coefficient prose: the logarithmic error is between
zero and two, with an absolute constant independent of the field and dimensions. -/
theorem prose_gaussian_logarithm_bounds (q a b : ℕ) (hq : 2 ≤ q) (hb : b ≤ a) :
    ((b * (a - b) : ℕ) : ℝ) ≤ Real.logb q (gaussianBinomial q a b : ℝ) ∧
      Real.logb q (gaussianBinomial q a b : ℝ) ≤ ((b * (a - b) : ℕ) : ℝ) + 2 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hp : (0 : ℝ) < q := by linarith
  have hg := gaussianBinomial_sharp_bounds q a b hq hb
  have hlo : (q : ℝ) ^ (b * (a - b)) ≤ (gaussianBinomial q a b : ℝ) := by
    exact_mod_cast hg.1
  have hgp : (0 : ℝ) < (gaussianBinomial q a b : ℝ) :=
    lt_of_lt_of_le (by positivity) hlo
  have hhi : (gaussianBinomial q a b : ℝ) ≤ (q : ℝ) ^ (b * (a - b) + 2) := by
    have hu : (gaussianBinomial q a b : ℝ) < 4 * (q : ℝ) ^ (b * (a - b)) := by
      exact_mod_cast hg.2
    have h4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by
      have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    rw [pow_add]
    exact hu.le.trans (by nlinarith [pow_pos hp (b * (a - b))])
  have hl := Real.logb_le_logb_of_le hqR (by positivity) hlo
  have hu := Real.logb_le_logb_of_le hqR hgp hhi
  simp only [Real.logb_pow, Real.logb_self_eq_one hqR, mul_one] at hl hu
  exact ⟨hl, by simpa using hu⟩

/-- Section 3.1's Gaussian logarithmic `O(1)` estimate, with explicit absolute
error at most two for the actual integral subspace count. -/
theorem prose_gaussian_logarithm_error (q a b : ℕ) (hq : 2 ≤ q) (hb : b ≤ a) :
    |Real.logb q (gaussianBinomial q a b : ℝ) - ((b * (a - b) : ℕ) : ℝ)| ≤ 2 := by
  obtain ⟨hl, hu⟩ := prose_gaussian_logarithm_bounds q a b hq hb
  rw [abs_le]
  constructor <;> linarith


/-- Section 3.1, line 150: each individual factor of the Gaussian product is
at least `q^(a-b)` when its index lies below the subspace dimension. -/
theorem prose_gaussian_product_factor_lower (q a b i : ℕ)
    (hq : 2 ≤ q) (hb : b ≤ a) (hi : i < b) :
    (q : ℝ) ^ (a - b) ≤ ((q : ℝ) ^ (a - i) - 1) / ((q : ℝ) ^ (b - i) - 1) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hd : (0 : ℝ) < (q : ℝ) ^ (b - i) - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ hqR (by omega))
  have hp : (1 : ℝ) ≤ (q : ℝ) ^ (a - b) := one_le_pow₀ hqR.le
  apply (le_div_iff₀ hd).mpr
  rw [show a - i = (a - b) + (b - i) by omega, pow_add]
  nlinarith

end BinaryFieldCounterexamples
