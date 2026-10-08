/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import BinaryFieldCounterexamples.Counting.GaussianEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Positivity of the fixed decision-tree multiplier

The concrete denominator is smaller than an elementary power lower bound on the
frame product, so its natural quotient is positive without any counting axiom.
-/
@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
theorem treeDenominator_pos (h : ℕ) : 0<treeDenominator h := by
  fun_induction treeDenominator h <;> positivity

theorem treeDenominator_le_pow (h : ℕ) (hh : 2≤h) :
    treeDenominator h ≤ 2^((2^h-1)*(2^h-1-1)) := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    obtain _|_|_|n := h
    · omega
    · omega
    · norm_num [treeDenominator]
    have hp : 1≤2^(n+2) := Nat.one_le_pow _ _ (by decide)
    let r := 2^(n+2)-1
    have hr : 1≤r := by
      have hp' : 2^2≤2^(n+2) := Nat.pow_le_pow_right (by decide) (by omega)
      dsimp [r]
      omega
    have ht : 2^(n+3)-1=2*r+1 := by
      dsimp [r]
      rw [show n+3=(n+2)+1 by omega,pow_succ]
      omega
    have hi := ih (n+2) (by omega) (by omega)
    change treeDenominator (n+2) ≤ 2^(r*(r-1)) at hi
    rw [treeDenominator,ht]
    change 2^(2*r)*treeDenominator (n+2)^2 ≤ _
    calc
      _ ≤ 2^(2*r)*(2^(r*(r-1)))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi 2)
      _ = 2^(2*r+r*(r-1)*2) := by simp only [pow_add,pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simp only [Nat.add_sub_cancel]; nlinarith [Nat.mul_le_mul_left r (Nat.sub_le r 1)])

theorem treeSupportCount_at_min_pos (h : ℕ) (hh : 2≤h) :
    0<treeSupportCount h (2^h-1) := by
  let r := 2^h-1
  have hr : 1≤r := by
    have hp : 2^2≤2^h := Nat.pow_le_pow_right (by decide) hh
    dsimp [r]
    omega
  have hprod := (binaryFrameProduct_bounds r r le_rfl).1
  have hquot : (2:ℝ)^r/2 = 2^(r-1) := by
    have heq : r=(r-1)+1 := by omega
    conv_lhs => rw [heq,pow_succ]
    ring
  rw [hquot,← pow_mul] at hprod
  have hp : 2^(r*(r-1)) ≤ binaryFrameProduct r r := by
    rw [Nat.mul_comm]
    exact_mod_cast hprod
  have hden := treeDenominator_le_pow h hh
  change treeDenominator h ≤ 2^(r*(r-1)) at hden
  change 0<binaryFrameProduct r r/treeDenominator h
  exact Nat.div_pos (hden.trans hp) (treeDenominator_pos h)
end BinaryFieldCounterexamples
