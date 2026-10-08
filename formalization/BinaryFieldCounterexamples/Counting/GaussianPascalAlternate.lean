/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianIdentities
import Mathlib.Tactic.Ring

/-!
# The alternate Gaussian Pascal recurrence

This file records the form of the Gaussian Pascal recurrence obtained by
adjoining the last coordinate rather than the first coordinate.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- The Gaussian Pascal recurrence with the power on the lower-rank term. -/
theorem gaussianPascal_succ_alt (q n k : ℕ) (hq : 1 < q) (hk : k ≤ n) :
    gaussianPascal q (n + 1) (k + 1) =
      q ^ (n - k) * gaussianPascal q n k + gaussianPascal q n (k + 1) := by
  by_cases he : k = n
  · subst k
    simp [gaussianPascal_self, gaussianPascal_eq_zero]
  · have hkn : k < n := by omega
    have hsL := gaussianPascal_symm q (n + 1) (k + 1) hq (by omega)
    have hs1 := gaussianPascal_symm q n (n - k - 1) hq (by omega)
    have hs2 := gaussianPascal_symm q n (n - k) hq (by omega)
    rw [show n + 1 - (k + 1) = n - k by omega] at hsL
    rw [show n - (n - k - 1) = k + 1 by omega] at hs1
    rw [show n - (n - k) = k by omega] at hs2
    rw [hsL, show n - k = (n - k - 1) + 1 by omega,
      gaussianPascal_succ, hs1, show n - k - 1 + 1 = n - k by omega, hs2]
    ring

end BinaryFieldCounterexamples
