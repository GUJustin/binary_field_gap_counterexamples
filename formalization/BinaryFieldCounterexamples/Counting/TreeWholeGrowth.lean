/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.PowerGrowth
public import BinaryFieldCounterexamples.Counting.TreePositivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-!
# Growth of unrestricted tree-support populations

The explicit frame-product quotient has exponent `2^h-1` at every fixed
height. The proof accounts for natural-number division using the concrete
positive denominator.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The unrestricted height-h support population has exponent `2^h-1`. -/
theorem treeSupportCount_growth (h : ℕ) (hh : 2 ≤ h) :
    HasBinaryPowerGrowth (treeSupportCount h) (2^h-1) := by
  let r := 2^h-1
  let δ := treeDenominator h
  have hr : 1 ≤ r := by
    have hp : 2^2 ≤ 2^h := Nat.pow_le_pow_right (by decide) hh
    dsimp [r]
    omega
  have hδ : 0 < δ := by dsimp [δ]; exact treeDenominator_pos h
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine ⟨(2^(r+1)*δ:ℝ)⁻¹, (δ:ℝ)⁻¹, by positivity, by positivity, r, ?_⟩
  intro d hd
  have hframe0 := (binaryFrameProduct_bounds r r le_rfl).1
  have hpform : ((2 : ℝ)^r/2)^r = (2:ℝ)^(r*(r-1)) := by
    have he : r=(r-1)+1 := by omega
    have hquot : (2 : ℝ)^r/2=2^(r-1) := by
      conv_lhs => rw [he,pow_succ]
      ring
    rw [hquot]
    rw [←pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [hpform] at hframe0
  have hpowframe : 2^(r*(r-1)) ≤ binaryFrameProduct r r := by exact_mod_cast hframe0
  have hδpow := treeDenominator_le_pow h hh
  change δ ≤ 2^(r*(r-1)) at hδpow
  have hδframe : δ ≤ binaryFrameProduct d r :=
    hδpow.trans (hpowframe.trans (binaryFrameProduct_mono r d r hd))
  have hdiv := nat_div_cast_bounds (binaryFrameProduct d r) δ hδ hδframe
  have hframe := binaryFrameProduct_bounds d r hd
  have hform : treeSupportCount h d = binaryFrameProduct d r / δ := by
    simp [treeSupportCount, binaryFrameProduct, r, δ]
  rw [hform]
  constructor
  · calc
      (2^(r+1)*δ:ℝ)⁻¹*(2^d:ℝ)^r = ((2:ℝ)^d/2)^r/(2*δ) := by
        rw [div_pow,pow_succ]
        field_simp
      _ ≤ (binaryFrameProduct d r:ℝ)/(2*δ) :=
        div_le_div_of_nonneg_right hframe.1 (by positivity)
      _ ≤ (binaryFrameProduct d r/δ:ℕ) := hdiv.1
  · calc
      ((binaryFrameProduct d r/δ:ℕ):ℝ) ≤ (binaryFrameProduct d r:ℝ)/δ := hdiv.2
      _ ≤ ((2:ℝ)^d)^r/δ := div_le_div_of_nonneg_right hframe.2 hδR.le
      _ = (δ:ℝ)⁻¹*(2^d:ℝ)^r := by field_simp

end BinaryFieldCounterexamples
