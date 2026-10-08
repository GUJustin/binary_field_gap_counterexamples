/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianBinomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Power bounds for the explicit binary Gaussian quotient

The estimates apply to the actual natural product quotient. A positive quotient
is within a factor of two of the corresponding real quotient, so these estimates
need no unproved divisibility or Gaussian subspace-counting identity.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
/-- The ordered-frame product shared by the Gaussian and tree counts. -/
def binaryFrameProduct (n r : ℕ) : ℕ := ∏ i ∈ Finset.range r, (2^n-2^i)
/-- Natural division differs from real division by at most a factor of two
once the numerator is at least the positive denominator. -/
theorem nat_div_cast_bounds (a b : ℕ) (hb : 0<b) (hab : b≤a) :
    (a : ℝ)/(2*b) ≤ (a/b : ℕ) ∧ (a/b : ℕ) ≤ (a : ℝ)/b := by
  have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hab)
  have hu : b*(a/b) ≤ a := Nat.mul_div_le a b
  have hl : a < b*(a/b+1) := Nat.lt_mul_div_succ a hb
  have hl' : a ≤ 2*b*(a/b) := by nlinarith
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*b)).mpr
    exact_mod_cast (by linarith [hl'] : a ≤ a/b*(2*b))
  · apply (le_div_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
    exact_mod_cast (by linarith [hu] : a/b*b≤a)

/-- Every fixed-length frame product has uniform two-sided power bounds. -/
theorem binaryFrameProduct_bounds (n r : ℕ) (hrn : r≤n) :
    ((2 : ℝ)^n/2)^r ≤ (binaryFrameProduct n r : ℝ) ∧
      (binaryFrameProduct n r : ℝ) ≤ ((2 : ℝ)^n)^r := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range r) :
      (2 : ℝ)^n/2 ≤ (2^n-2^i : ℕ) ∧ (2^n-2^i : ℕ) ≤ (2 : ℝ)^n := by
    have hin : i+1≤n := by have := Finset.mem_range.mp hi; omega
    have hp : 2*2^i ≤ 2^n := by
      have := Nat.pow_le_pow_right (by decide : 0<2) hin
      simpa [pow_succ, Nat.mul_comm] using this
    have hs : 2^i≤2^n := by omega
    have hc : ((2^n-2^i : ℕ):ℝ)=(2:ℝ)^n-(2:ℝ)^i := by
      rw [Nat.cast_sub hs]
      norm_cast
    rw [hc]
    have hpr : 2*(2:ℝ)^i≤(2:ℝ)^n := by exact_mod_cast hp
    constructor
    · linarith
    · have : (0:ℝ)≤2^i := by positivity
      linarith
  have hl : (∏ i ∈ Finset.range r, (2 : ℝ)^n/2) ≤
      ∏ i ∈ Finset.range r, ((2^n-2^i : ℕ):ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi; exact (hterm i hi).1
  have hu : (∏ i ∈ Finset.range r, ((2^n-2^i : ℕ):ℝ)) ≤
      ∏ i ∈ Finset.range r, (2:ℝ)^n := by
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi; exact (hterm i hi).2
  constructor
  · simpa [binaryFrameProduct, div_pow] using hl
  · simpa [binaryFrameProduct] using hu
/-- In the valid range each ordered-frame factor is positive. -/
theorem binaryFrameProduct_pos (n r : ℕ) (hrn : r≤n) :
    0<binaryFrameProduct n r := by
  apply Finset.prod_pos
  intro i hi
  apply Nat.sub_pos_of_lt
  apply Nat.pow_lt_pow_right (by decide)
  have := Finset.mem_range.mp hi
  omega

/-- Increasing the ambient dimension increases the ordered-frame product. -/
theorem binaryFrameProduct_mono (n m r : ℕ) (hnm : n≤m) :
    binaryFrameProduct n r ≤ binaryFrameProduct m r := by
  apply Finset.prod_le_prod
  intro i hi
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0<2) hnm) _

/-- Uniform Gaussian bounds use its literal natural quotient and require no
unproved integrality or subspace counting formula. -/
theorem gaussianBinomial_two_bounds (n r : ℕ) (hrn : r≤n) :
    ((2:ℝ)^n)^r / (2^(r+1)*(binaryFrameProduct r r : ℝ)) ≤ gaussianBinomial 2 n r ∧
      (gaussianBinomial 2 n r : ℝ) ≤ ((2:ℝ)^n)^r / binaryFrameProduct r r := by
  have hden := binaryFrameProduct_pos r r le_rfl
  have hnum := binaryFrameProduct_mono r n r hrn
  have hdiv := nat_div_cast_bounds (binaryFrameProduct n r) (binaryFrameProduct r r) hden hnum
  have hprod := binaryFrameProduct_bounds n r hrn
  have hdenR : (0:ℝ)<binaryFrameProduct r r := by exact_mod_cast hden
  have hform : gaussianBinomial 2 n r=binaryFrameProduct n r/binaryFrameProduct r r := by
    simp [gaussianBinomial, hrn, binaryFrameProduct]
  rw [hform]
  constructor
  · apply le_trans _ hdiv.1
    calc
      _ = ((2:ℝ)^n/2)^r/(2*(binaryFrameProduct r r:ℝ)) := by
        rw [div_pow,pow_succ]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hprod.1 (by positivity)
  · exact hdiv.2.trans (div_le_div_of_nonneg_right hprod.2 (by positivity))
end BinaryFieldCounterexamples
