/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianSharpBound
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The strict infinite-product bound in Section 3

A uniform lower bound `9/32` for finite binary denominator products remains
strictly greater than `1/4` in the limit. This proves the literal infinite
product claim, including convergence, rather than just the finite Gaussian bound.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators Topology
open Filter

theorem binary_partial_product_lower (k : ℕ) :
    (9/32 : ℝ) + (3/8 : ℝ)*(1/2 : ℝ)^(k+2) ≤
      ∏ i ∈ Finset.range (k+2), (1-(1/2 : ℝ)^(i+1)) := by
  induction k with
  | zero => norm_num [Finset.prod_range_succ]
  | succ k ih =>
    rw [show k+1+2=(k+2)+1 by omega, Finset.prod_range_succ]
    have hx : 0 ≤ (1/2 : ℝ)^(k+2) := by positivity
    have hxle : (1/2 : ℝ)^(k+2) ≤ 1/4 := by
      have h := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) ≤ 1) (show 2 ≤ k+2 by omega)
      norm_num at h
      exact h
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right ih
      (show 0 ≤ 1-(1/2:ℝ)^(k+2)*(1/2) by linarith)
    nlinarith [mul_nonneg hx (show 0 ≤ 1/4-(1/2:ℝ)^(k+2) by linarith)]

/-- Section 3's Gaussian size paragraph: every finite denominator product is
at least `9/32`, a uniform bound that is strictly above `1/4`. -/
theorem gaussian_denominatorProduct_ge_nine_thirtytwo (q n : ℕ) (hq : 2 ≤ q) :
    (9/32 : ℝ) ≤ ∏ i ∈ Finset.range n, (1-(1/(q:ℝ))^(i+1)) := by
  have hbinary : (9/32 : ℝ) ≤ ∏ i ∈ Finset.range n, (1-(1/2:ℝ)^(i+1)) := by
    rcases n with _ | (_ | k)
    · norm_num
    · norm_num [Finset.prod_range_succ]
    · have h := binary_partial_product_lower k
      have hp : 0 ≤ (3/8 : ℝ)*(1/2:ℝ)^(k+2) := by positivity
      have hh : (9/32:ℝ) ≤ ∏ i ∈ Finset.range (k+2), (1-(1/2:ℝ)^(i+1)) := by linarith
      convert hh using 2
  apply hbinary.trans
  apply Finset.prod_le_prod₀
  · intro i hi
    have := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := i+1)
    linarith
  · intro i hi
    have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
    have hb : 1/(q:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hqR
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(q:ℝ)) hb (i+1)
    linarith

/-- Section 3's Gaussian size paragraph: the infinite product over `j ≥ 1`
of `(1-q⁻ʲ)⁻¹` converges and is strictly less than four for every integer `q ≥ 2`. -/
theorem gaussian_inverse_infiniteProduct_lt_four (q : ℕ) (hq : 2 ≤ q) :
    Multipliable (fun i : ℕ ↦ (1-(1/(q:ℝ))^(i+1))⁻¹) ∧
      (∏' i : ℕ, (1-(1/(q:ℝ))^(i+1))⁻¹) < 4 := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hb0 : 0 ≤ 1/(q:ℝ) := by positivity
  have hb1 : 1/(q:ℝ) < 1 := by
    apply (div_lt_one (by linarith : (0:ℝ) < q)).2
    linarith
  have hs : Summable (fun i : ℕ ↦ (1/(q:ℝ))^(i+1)) := by
    exact (summable_geometric_of_lt_one hb0 hb1).mul_right (1/(q:ℝ)) |>.congr
      (fun i ↦ (pow_succ _ _).symm)
  have hm : Multipliable (fun i : ℕ ↦ 1-(1/(q:ℝ))^(i+1)) := by
    simpa [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs.neg
  have hlow : (9/32 : ℝ) ≤ ∏' i : ℕ, (1-(1/(q:ℝ))^(i+1)) :=
    ge_of_tendsto' hm.tendsto_prod_tprod_nat (fun n ↦ gaussian_denominatorProduct_ge_nine_thirtytwo q n hq)
  have hpos : (0:ℝ) < ∏' i : ℕ, (1-(1/(q:ℝ))^(i+1)) := by linarith
  refine ⟨hm.inv₀ hpos.ne', ?_⟩
  rw [hm.tprod_inv₀ hpos.ne']
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ hpos).2
  linarith

end BinaryFieldCounterexamples
