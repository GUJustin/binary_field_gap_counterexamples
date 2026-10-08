/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianBinomial

/-!
# Concrete decision-tree support count formulas

These are the original explicit natural-number formulas used by Theorem 6.10
and Corollary 6.7. Their numerical asymptotics can be proved independently of
the finite-field support construction. The concrete support families and their
cardinality proofs are in `Constructions.Trees.TemplateCounts` and
`Constructions.Trees.AvoidingCounts`; both constructions are proved.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The exact denominator in the balanced-tree support count; heights zero
and one are unused by the theorem and assigned the value one. -/
def treeDenominator : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | n + 3 => 2 ^ (2 * (2 ^ (n + 2) - 1)) * treeDenominator (n + 2) ^ 2

/-- Number of balanced height-`h` supports on a binary `d`-space, as the
explicit product in Lemma 6.6; used only under `2 ≤ h` and `2^h - 1 ≤ d`. -/
def treeSupportCount (h d : ℕ) : ℕ :=
  (∏ i ∈ Finset.range (2 ^ h - 1), (2 ^ d - 2 ^ i)) / treeDenominator h

/-- Exact support recursion in Theorem 6.10. The unused heights zero and one
are assigned zero; no existence or counting assertion is hidden here. -/
def avoidingTreeSupportCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | 2, d => 28 * (6 * 2 ^ (d - 3) - 5)
  | n + 3, d =>
      let r : ℕ := 2 ^ (n + 2) - 1
      (2 ^ (n + 4) - 1) * avoidingTreeSupportCount (n + 2) (d - 1) *
        2 ^ (r ^ 2) * gaussianBinomial 2 (d - 1 - r) r * treeSupportCount (n + 2) r

end BinaryFieldCounterexamples
