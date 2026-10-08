/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianBinomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
/-!
# Exact arithmetic for the Longfellow parameter choices

This module records the finite arithmetic used by the Longfellow construction:
the explicit Gaussian list size, its four exponent/threshold choices, the
capacity comparison outside the exceptional set, and the central interval
inclusion. All statements are proved by kernel-checked numeral computation.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow

/-- The list size `16 (2^6 - 1) [5 choose 2]_4` in the construction. -/
def listSize : ℕ := 16 * (2 ^ 6 - 1) * BinaryFieldCounterexamples.gaussianBinomial 4 5 2

/-- The explicit Gaussian product evaluates to the list size used below. -/
theorem listSize_value : listSize = 5843376 := by
  norm_num [listSize, BinaryFieldCounterexamples.gaussianBinomial,
    Finset.prod_range_succ]

/-- The encoded length `e`, message length `K`, queried length `N`, padding `w`,
and agreement threshold `T` for a given encoded length. -/
def parameters (e : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (e, (e + 1) / 9, e - 2 * ((e + 1) / 9) + 1,
    (e + 1) / 9 - 384, (e + 1) / 9 + 384)

theorem parameters_4151 : parameters 4151 = (4151, 461, 3230, 77, 845) := by
  norm_num [parameters]

theorem parameters_4265 : parameters 4265 = (4265, 474, 3318, 90, 858) := by
  norm_num [parameters]

theorem parameters_4307 : parameters 4307 = (4307, 478, 3352, 94, 862) := by
  norm_num [parameters]

theorem parameters_4415 : parameters 4415 = (4415, 490, 3436, 106, 874) := by
  norm_num [parameters]

/-- The four `(queried length, message length)` pairs used by the construction. -/
def parameterPairs : Finset (ℕ × ℕ) :=
  {(3230, 461), (3318, 474), (3352, 478), (3436, 490)}

/-- Every configured pair satisfies the padding, containment, and 128-bit
exterior-pole budget inequalities required by the assembly theorem. -/
theorem configured_parameter_bounds {S K : ℕ} (h : (S, K) ∈ parameterPairs) :
    384 ≤ K ∧ K ≤ S ∧ K - 384 ≤ S - 2048 ∧
      S + K * (Nat.choose listSize 2 + listSize) < 2 ^ 128 := by
  simp only [parameterPairs, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at h
  rcases h with h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals rw [listSize_value, Nat.choose_two_right]
  all_goals norm_num

/-- The list size times the collision-pair plus singleton bound fits outside
the exceptional set of size `N` in the 128-bit ambient space. -/
theorem exterior_pole_budget_4151 :
    461 * (Nat.choose listSize 2 + listSize) < 2 ^ 128 - 3230 := by
  rw [listSize_value]
  rw [Nat.choose_two_right]
  norm_num

theorem exterior_pole_budget_4265 :
    474 * (Nat.choose listSize 2 + listSize) < 2 ^ 128 - 3318 := by
  rw [listSize_value]
  rw [Nat.choose_two_right]
  norm_num

theorem exterior_pole_budget_4307 :
    478 * (Nat.choose listSize 2 + listSize) < 2 ^ 128 - 3352 := by
  rw [listSize_value]
  rw [Nat.choose_two_right]
  norm_num

theorem exterior_pole_budget_4415 :
    490 * (Nat.choose listSize 2 + listSize) < 2 ^ 128 - 3436 := by
  rw [listSize_value]
  rw [Nat.choose_two_right]
  norm_num

/-- Every integer in `[2048, 4096)` belongs to the construction's interval
`[2K - 1, e)` for this parameter choice. -/
theorem central_interval_4151 :
    ∀ x : ℕ, 2048 ≤ x → x < 4096 → 2 * 461 - 1 ≤ x ∧ x < 4151 := by
  intro x hx₁ hx₂
  constructor
  · exact Nat.le_trans (by norm_num) hx₁
  · exact Nat.lt_trans hx₂ (by norm_num)

theorem central_interval_4265 :
    ∀ x : ℕ, 2048 ≤ x → x < 4096 → 2 * 474 - 1 ≤ x ∧ x < 4265 := by
  intro x hx₁ hx₂
  constructor
  · exact Nat.le_trans (by norm_num) hx₁
  · exact Nat.lt_trans hx₂ (by norm_num)

theorem central_interval_4307 :
    ∀ x : ℕ, 2048 ≤ x → x < 4096 → 2 * 478 - 1 ≤ x ∧ x < 4307 := by
  intro x hx₁ hx₂
  constructor
  · exact Nat.le_trans (by norm_num) hx₁
  · exact Nat.lt_trans hx₂ (by norm_num)

theorem central_interval_4415 :
    ∀ x : ℕ, 2048 ≤ x → x < 4096 → 2 * 490 - 1 ≤ x ∧ x < 4415 := by
  intro x hx₁ hx₂
  constructor
  · exact Nat.le_trans (by norm_num) hx₁
  · exact Nat.lt_trans hx₂ (by norm_num)

end BinaryFieldCounterexamples.Longfellow
