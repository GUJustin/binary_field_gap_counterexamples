/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.ExactRetentionProbability

/-!
# The uniform factor-four bound for Gaussian coefficients

The size clause of the Gaussian-binomial paragraph in manuscript Section 3
(`sec:gaussian-binomials`, `sections/preliminaries.tex`) states
`q^(b*(a-b)) ≤ [a choose b]_q < 4*q^(b*(a-b))`.
Here the bound holds for every integer base `q ≥ 2`, including the boundary
ranks `b = 0` and `b = a`. The strict upper bound comes from comparing its
finite denominator product with the binary product, which is strictly above
one quarter.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The finite denominator product for any integer base at least two is
strictly above one quarter, uniformly in the number of factors. -/
theorem gaussian_denominatorProduct_gt_quarter (q k : ℕ) (hq : 2 ≤ q) :
    (1/4 : ℚ) < ∏ i ∈ Finset.range k, (1 - (1/(q:ℚ))^(i+1)) := by
  have hqQ : (2:ℚ) ≤ q := by exact_mod_cast hq
  have hcomp : (∏ i ∈ Finset.range k, (1-(1/2:ℚ)^(i+1))) ≤
      ∏ i ∈ Finset.range k, (1-(1/(q:ℚ))^(i+1)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have h := pow_le_one₀ (by norm_num : (0:ℚ) ≤ 1/2)
        (by norm_num : (1/2:ℚ) ≤ 1) (n := i+1)
      linarith
    · intro i hi
      have hbase : (1/(q:ℚ)) ≤ (1/2:ℚ) :=
        one_div_le_one_div_of_le (by norm_num) hqQ
      have hpow := pow_le_pow_left₀ (by positivity : (0:ℚ) ≤ 1/(q:ℚ)) hbase (i+1)
      linarith
  apply lt_of_lt_of_le _ hcomp
  cases k with
  | zero => norm_num
  | succ k =>
    have hp : (0:ℚ) < (1/2:ℚ)^(k+2) := by positivity
    linarith [binary_retention_product_lower k]

/-- The Gaussian product is at most its leading power divided by the finite
normalized denominator product. -/
theorem quadraticGaussian_le_pow_div_denominatorProduct (q a b : ℕ)
    (hq : 2 ≤ q) (hb : b ≤ a) :
    quadraticGaussian q a b ≤
      (q:ℚ)^(b*(a-b)) / (∏ i ∈ Finset.range b, (1-(1/(q:ℚ))^(i+1))) := by
  have hqQ : (1:ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hprod : quadraticGaussian q a b ≤
      ∏ i ∈ Finset.range b, (q:ℚ)^(a-b)/(1-(1/(q:ℚ))^(b-i)) := by
    unfold quadraticGaussian
    apply Finset.prod_le_prod₀
    · intro i hi
      have hir : i < b := Finset.mem_range.mp hi
      have ha : (1:ℚ) < (q:ℚ)^(a-i) := one_lt_pow₀ hqQ (by omega)
      have hb' : (1:ℚ) < (q:ℚ)^(b-i) := one_lt_pow₀ hqQ (by omega)
      exact div_nonneg (by linarith) (by linarith)
    · intro i hi
      have hir : i < b := Finset.mem_range.mp hi
      have hp : (1:ℚ) < (q:ℚ)^(b-i) := one_lt_pow₀ hqQ (by omega)
      have he : (q:ℚ)^(a-i) = (q:ℚ)^(a-b)*(q:ℚ)^(b-i) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        ((q:ℚ)^(a-i)-1)/((q:ℚ)^(b-i)-1) ≤
            (q:ℚ)^(a-i)/((q:ℚ)^(b-i)-1) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ = (q:ℚ)^(a-b)/(1-(1/(q:ℚ))^(b-i)) := by
          rw [one_div_pow, he]
          field_simp
  have hreflect : (∏ i ∈ Finset.range b, (1-(1/(q:ℚ))^(b-i))) =
      ∏ i ∈ Finset.range b, (1-(1/(q:ℚ))^(i+1)) := by
    rw [← Finset.prod_range_reflect (fun i => 1-(1/(q:ℚ))^(i+1)) b]
    apply Finset.prod_congr rfl
    intro i hi
    congr 2
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.prod_div_distrib, hreflect] at hprod
  simpa [← pow_mul, Nat.mul_comm] using hprod

/-- The Gaussian-binomial size clause in manuscript Section 3, for every
integer `q ≥ 2` and every admissible rank `b ≤ a`: the upper constant four is
strict and independent of all three parameters. -/
theorem gaussianBinomial_sharp_bounds (q a b : ℕ) (hq : 2 ≤ q) (hb : b ≤ a) :
    q^(b*(a-b)) ≤ gaussianBinomial q a b ∧
      gaussianBinomial q a b < 4*q^(b*(a-b)) := by
  constructor
  · exact pow_mul_sub_le_gaussianBinomial q a b (by omega) hb
  · have hden := gaussian_denominatorProduct_gt_quarter q b hq
    have hup := quadraticGaussian_le_pow_div_denominatorProduct q a b hq hb
    have hpow : (0:ℚ) < (q:ℚ)^(b*(a-b)) := by positivity
    have hstrict : quadraticGaussian q a b < 4*(q:ℚ)^(b*(a-b)) := by
      apply lt_of_le_of_lt hup
      apply (div_lt_iff₀ (show (0:ℚ) < ∏ i ∈ Finset.range b,
        (1-(1/(q:ℚ))^(i+1)) by linarith)).mpr
      nlinarith
    rw [← cast_gaussianBinomial_eq_quadraticGaussian q a b (by omega) hb] at hstrict
    exact_mod_cast hstrict

end BinaryFieldCounterexamples
