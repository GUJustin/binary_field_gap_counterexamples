/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.ExactRetention
public import BinaryFieldCounterexamples.Counting.GaussianLowerBound
/-!
# Product formula and uniform lower bound for exact padding retention

The Gaussian success probability is a product of `r` elementary factors.
It stays strictly above one quarter throughout `r ≤ w ≤ d`, including
the boundary where the union-bound estimate can vanish asymptotically.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- Every admissible binary Gaussian coefficient is strictly positive. -/
theorem binaryGaussian_pos (n k : ℕ) (hk : k≤n) :
    (0:ℚ) < gaussianBinomial 2 n k := by
  have h := pow_mul_sub_le_gaussianBinomial 2 n k (by decide) hk
  have hp : 0 < (2:ℕ)^(k*(n-k)) := by positivity
  exact_mod_cast hp.trans_le h

/-- Flag counting rewrites the exact probability using only `r` factors. -/
theorem paddingRetentionProbability_flag (d w r : ℕ) (hrw : r≤w) (hwd : w≤d) :
    paddingRetentionProbability d w r =
      (2:ℚ)^(r*(d-w)) * gaussianBinomial 2 w r / gaussianBinomial 2 d r := by
  have hf := gaussianBinomial_flag 2 d w r (by decide) hwd hrw
  have hfq : (gaussianBinomial 2 d w:ℚ)*gaussianBinomial 2 w r =
      (gaussianBinomial 2 d r:ℚ)*gaussianBinomial 2 (d-r) (w-r) := by exact_mod_cast hf
  have hw0 := (binaryGaussian_pos d w hwd).ne'
  have hr0 := (binaryGaussian_pos d r (hrw.trans hwd)).ne'
  unfold paddingRetentionProbability
  field_simp
  linarith [hfq]

/-- The Gaussian ratio is the product of the exact spanning probabilities. -/
theorem paddingRetentionProbability_product (d w r : ℕ) (hrw : r≤w) (hwd : w≤d) :
    paddingRetentionProbability d w r =
      ∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(w-i))/(1-(1/2:ℚ)^(d-i)) := by
  rw [paddingRetentionProbability_flag d w r hrw hwd,
    cast_gaussianBinomial_eq_quadraticGaussian 2 w r (by decide) hrw,
    cast_gaussianBinomial_eq_quadraticGaussian 2 d r (by decide) (hrw.trans hwd)]
  unfold quadraticGaussian
  rw [mul_div_assoc,←Finset.prod_div_distrib]
  have he : (2:ℚ)^(r*(d-w)) = ∏ _i ∈ Finset.range r, (2:ℚ)^(d-w) := by
    simp [←pow_mul,Nat.mul_comm]
  rw [he,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i<r := Finset.mem_range.mp hi
  have hrp : 1 < (2:ℚ)^(r-i) := one_lt_pow₀ (by norm_num) (by omega)
  have hwp : 1 < (2:ℚ)^(w-i) := one_lt_pow₀ (by norm_num) (by omega)
  have hdp : 1 < (2:ℚ)^(d-i) := one_lt_pow₀ (by norm_num) (by omega)
  have hexp : (2:ℚ)^(d-i) = 2^(d-w)*2^(w-i) := by
    rw [←pow_add]
    congr 1
    omega
  rw [one_div_pow,one_div_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp [sub_ne_zero.mpr hrp.ne',sub_ne_zero.mpr hdp.ne']
  nlinarith [hexp]

/-- An elementary positive remainder keeps every finite binary product above one quarter. -/
theorem binary_retention_product_lower (k : ℕ) :
    (1/4:ℚ)+(1/2:ℚ)^(k+2) ≤
      ∏ i ∈ Finset.range (k+1), (1-(1/2:ℚ)^(i+1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hx : 0 ≤ (1/2:ℚ)^(k+2) := by positivity
    have hxle : (1/2:ℚ)^(k+2) ≤ 1/4 := by
      have h := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤1/2)
        (by norm_num : (1/2:ℚ)≤1) (show 2≤k+2 by omega)
      norm_num at h ⊢
      exact h
    have hm := mul_le_mul_of_nonneg_right ih (show 0≤1-(1/2:ℚ)^(k+2) by linarith)
    have hp : (1/2:ℚ)^(k+1+2)=(1/2:ℚ)^(k+2)/2 := by
      rw [show k+1+2=(k+2)+1 by omega,pow_succ]
      ring
    rw [hp]
    linarith [mul_nonneg hx (sub_nonneg.mpr hxle)]

/-- Exact padding retains a constant fraction even at the smallest allowed padding dimension. -/
theorem paddingRetentionProbability_gt_quarter (d w r : ℕ) (hrw : r≤w) (hwd : w≤d) :
    (1/4:ℚ) < paddingRetentionProbability d w r := by
  rw [paddingRetentionProbability_product d w r hrw hwd]
  have hcomp : (∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(r-i))) ≤
      ∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(w-i))/(1-(1/2:ℚ)^(d-i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hpow := pow_le_one₀ (by norm_num : (0:ℚ)≤1/2) (by norm_num : (1/2:ℚ)≤1) (n:=r-i)
      linarith
    · intro i hi
      have hir : i<r := Finset.mem_range.mp hi
      have hdp : (1/2:ℚ)^(d-i)<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have hwp := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤1/2)
        (by norm_num : (1/2:ℚ)≤1) (show r-i≤w-i by omega)
      have hrp : (1/2:ℚ)^(r-i)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hpos : 0≤(1/2:ℚ)^(d-i) := by positivity
      apply (le_div_iff₀ (show 0<1-(1/2:ℚ)^(d-i) by linarith)).mpr
      linarith [mul_nonneg (sub_nonneg.mpr hrp) hpos]
  have hreflect : (∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(r-i))) =
      ∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(i+1)) := by
    rw [←Finset.prod_range_reflect (fun i => 1-(1/2:ℚ)^(i+1)) r]
    apply Finset.prod_congr rfl
    intro i hi
    congr 2
    have := Finset.mem_range.mp hi
    omega
  rw [hreflect] at hcomp
  apply lt_of_lt_of_le _ hcomp
  cases r with
  | zero => norm_num
  | succ k =>
    have hp : (0:ℚ)<(1/2:ℚ)^(k+2) := by positivity
    linarith [binary_retention_product_lower k]
end BinaryFieldCounterexamples
