/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
import Mathlib.Tactic.Ring
/-!
# A power lower bound for Gaussian coefficients
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- The integral Gaussian coefficient contains at least its leading power. -/
theorem pow_mul_sub_le_gaussianPascal (q n k : ℕ) (hk : k≤n) :
    q^(k*(n-k)) ≤ gaussianPascal q n k := by
  induction n generalizing k with
  | zero =>
      have : k=0 := by omega
      subst k
      simp [gaussianPascal]
  | succ n ih =>
      cases k with
      | zero => simp [gaussianPascal_zero]
      | succ k =>
          by_cases hkn : k=n
          · subst k
            simp [gaussianPascal_self]
          have hk' : k+1≤n := by omega
          rw [gaussianPascal_succ]
          apply le_add_of_le_right
          have hs : n+1-(k+1)=n-k := by omega
          have hs' : n-(k+1)+1=n-k := by omega
          have he : (k+1)*(n+1-(k+1))=(k+1)+(k+1)*(n-(k+1)) := by
            rw [hs,←hs']
            ring
          rw [he,pow_add]
          exact Nat.mul_le_mul_left _ (ih (k+1) hk')

/-- For base greater than one, the paper's natural Gaussian coefficient is at
least `q^(k*(n-k))`. -/
theorem pow_mul_sub_le_gaussianBinomial (q n k : ℕ) (hq : 1<q) (hk : k≤n) :
    q^(k*(n-k)) ≤ gaussianBinomial q n k := by
  rw [gaussianBinomial_eq_gaussianPascal q n k hq]
  exact pow_mul_sub_le_gaussianPascal q n k hk

end BinaryFieldCounterexamples
