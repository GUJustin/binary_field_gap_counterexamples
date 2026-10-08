/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Johnson placement and collision specializations at rate 1/16

The arithmetic following Theorem 4.1 places the largest integer below the
Johnson threshold and computes its gap above common agreement. Corollary 4.2
specializes its two simultaneous collision bounds without changing the pair.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- Theorem 4.1, Johnson-placement paragraph: the integer squares strictly
sandwich `N(K−1)` when `N=16K` and `K≥2`. -/
theorem quadratic_johnson_squared_bounds (K : ℕ) (hK : 2 ≤ K) :
    (4 * K - 3) ^ 2 < 16 * K * (K - 1) ∧
      16 * K * (K - 1) < (4 * K - 2) ^ 2 := by
  have ha : 4 * K - 3 + 3 = 4 * K := by omega
  have hb : 4 * K - 2 + 2 = 4 * K := by omega
  have hc : K - 1 + 1 = K := by omega
  constructor <;> nlinarith

/-- Theorem 4.1 and Section 4's subspace-locator summary: `4K−3` is precisely
the largest integer strictly below Johnson and its common-agreement gap is
`2K−2 = N/8−2`. -/
theorem quadratic_johnson_largest_integer_and_gap (K : ℕ) (hK : 2 ≤ K) :
    ((4 * K - 3 : ℕ) : ℝ) < Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ) ∧
    Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ) < ((4 * K - 2 : ℕ) : ℝ) ∧
    (∀ m : ℕ, (m : ℝ) < Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ) ↔
      m ≤ 4 * K - 3) ∧
    (4 * K - 3) - (2 * K - 1) = 2 * K - 2 ∧
    2 * K - 2 = (16 * K) / 8 - 2 := by
  obtain ⟨hlo, hhi⟩ := quadratic_johnson_squared_bounds K hK
  have hloR : ((4 * K - 3 : ℕ) : ℝ) ^ 2 < ((16 * K * (K - 1) : ℕ) : ℝ) := by
    exact_mod_cast hlo
  have hhiR : ((16 * K * (K - 1) : ℕ) : ℝ) < ((4 * K - 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hhi
  have hslo := Real.lt_sqrt_of_sq_lt hloR
  have hshi : Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ) < ((4 * K - 2 : ℕ) : ℝ) :=
    (Real.sqrt_lt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hhiR
  refine ⟨hslo, hshi, ?_, by omega, by omega⟩
  intro m
  constructor
  · intro hm
    have hm' : m < 4 * K - 2 := by exact_mod_cast hm.trans hshi
    omega
  · intro hm
    exact (Nat.cast_le.mpr hm).trans_lt hslo

/-- Corollary 4.2, first “in particular” clause: the ceiling collision bound
is strictly greater than `M/2` when the challenge field has size at least `M`. -/
theorem quadratic_collision_ceiling_gt_half (M q : ℕ) (hM : 0 < M)
    (hqM : M ≤ q) :
    (M : ℚ) / 2 < (⌈(q : ℚ) * M / (q + M - 1)⌉₊ : ℚ) := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hq : (M : ℚ) ≤ q := by exact_mod_cast hqM
  have hd : (0 : ℚ) < q + M - 1 := by
    have hM1 : (1 : ℚ) ≤ M := by exact_mod_cast hM
    linarith
  have hratio : (M : ℚ) / 2 < (q : ℚ) * M / (q + M - 1) := by
    rw [lt_div_iff₀ hd]
    nlinarith
  exact hratio.trans_le (Nat.le_ceil _)

/-- Corollary 4.2, second “in particular” clause: if the field size exceeds
all unordered locator pairs, the floor collision loss vanishes. -/
theorem quadratic_collision_floor_eq_zero (M q : ℕ) (hq : Nat.choose M 2 < q) :
    M - ⌊(Nat.choose M 2 : ℚ) / q⌋₊ = M := by
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hf : ⌊(Nat.choose M 2 : ℚ) / q⌋₊ = 0 := by
    apply Nat.floor_eq_zero.mpr
    rw [div_lt_one hqpos]
    exact_mod_cast hq
  rw [hf, Nat.sub_zero]

end BinaryFieldCounterexamples
