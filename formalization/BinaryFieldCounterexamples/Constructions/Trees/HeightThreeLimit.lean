/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.HeightThreeFormula
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The exact height-three asymptotic constant

Section 6.3's `M₃(d) ∼ (105/16)2^(4d)` follows from the closed product.
This theorem gives the literal normalized-count limit, so the leading
coefficient is attached to the actual recursive population.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Filter Topology

/-- Section 6.3: the actual avoiding-tree population divided by `2^(4d)`
tends to exactly `105/16`. -/
theorem avoidingTreeSupportCount_three_limit :
    Tendsto (fun d : ℕ => (avoidingTreeSupportCount 3 d : ℝ)/(2 : ℝ)^(4*d))
      atTop (𝓝 (105/16 : ℝ)) := by
  have hi : Tendsto (fun d : ℕ => ((2 : ℝ)^d)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hf : Tendsto (fun d : ℕ =>
      71680 * ((6/16 : ℝ)-5*((2 : ℝ)^d)⁻¹) *
      ((1/16 : ℝ)-((2 : ℝ)^d)⁻¹) *
      ((1/16 : ℝ)-2*((2 : ℝ)^d)⁻¹) *
      ((1/16 : ℝ)-4*((2 : ℝ)^d)⁻¹)) atTop (𝓝 (105/16 : ℝ)) := by
    convert ((tendsto_const_nhds.mul (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul hi))).mul (tendsto_const_nhds.sub hi)).mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hi)) |>.mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hi)) using 1 <;> norm_num
  apply hf.congr'
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with d hd
  rw [avoidingTreeSupportCount_three_closed d hd]
  have hw : 8 ≤ (2 : ℕ)^(d-4) := by
    calc 8=2^3 := by norm_num
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub (by omega : 5 ≤ 6*2^(d-4)),Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ 2^(d-4)),Nat.cast_sub (by omega : 2 ≤ 2^(d-4)),
    Nat.cast_sub (by omega : 4 ≤ 2^(d-4))]
  norm_num only [Nat.cast_ofNat,Nat.cast_pow]
  have hp : (2 : ℝ)^d = 16*(2 : ℝ)^(d-4) := by
    conv_lhs => rw [show d=(d-4)+4 by omega]
    rw [pow_add]; norm_num; ring
  rw [show 4*d=d*4 by omega,pow_mul]
  have hn : (2 : ℝ)^d ≠ 0 := by positivity
  field_simp
  rw [hp]
  ring
end BinaryFieldCounterexamples
