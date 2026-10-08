/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Finset.Range

/-!
# Gaussian coefficient expressions used in the theorem contracts

These are explicit finite product formulas, not assumed counting laws. Integrality
and their correspondence to subspace counts remain proof obligations. The natural
formula clips out-of-range dimensions; the rational formula is used only in the
valid parameter range of the quadratic-form theorem.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- Gaussian binomial coefficient, given by its exact finite product quotient.
The out-of-range value is zero. No counting theorem is assumed in this definition. -/
def gaussianBinomial (q n k : ℕ) : ℕ :=
  if k ≤ n then
    (∏ i ∈ Finset.range k, (q ^ n - q ^ i)) /
      (∏ i ∈ Finset.range k, (q ^ k - q ^ i))
  else 0

/-- Gaussian coefficient in the exact finite count, written as its product
formula over the rationals (integrality is part of the eventual proof). -/
noncomputable def quadraticGaussian (q n t : ℕ) : ℚ :=
  ∏ i ∈ Finset.range t, ((q : ℚ) ^ (n - i) - 1) / ((q : ℚ) ^ (t - i) - 1)


end BinaryFieldCounterexamples
