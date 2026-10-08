/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.TreeAsymptotics
/-!
# Main theorem companion: fixed-height support-count asymptotics

The numerical assertion in Theorem 6.10, p. 63 is proved for the original exact
support recursion. For each fixed height `h≥3`, positive constants and a dimension
cutoff are chosen before the growing dimension; the exponent is `2^h-h-1`.
This numerical assertion is independent of the finite-field decision-tree
construction and its probability conclusions in `HalfRateDecisionTrees.lean`.
Those companion conclusions are also proved, from concrete support families,
locator polynomials, and exterior-pole collision bounds.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- Theorem 6.10, support-count asymptotics: constants depend only on height. -/
theorem half_rate_support_count_asymptotic (h : ℕ) (hh : 3 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → 2 ^ h - 1 ≤ d →
        c * (2 ^ d : ℝ) ^ (2 ^ h - h - 1) ≤ avoidingTreeSupportCount h d ∧
        (avoidingTreeSupportCount h d : ℝ) ≤ C * (2 ^ d : ℝ) ^ (2 ^ h - h - 1) := by
  obtain ⟨c,C,hc,hC,d₀,hbounds⟩ := avoidingTreeSupportCount_growth h (by omega)
  exact ⟨c,C,hc,hC,d₀,fun d hd _ => hbounds d hd⟩

end BinaryFieldCounterexamples
