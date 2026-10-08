/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.AnisotropicGroupedKernel
public import BinaryFieldCounterexamples.Counting.GaussianBackwardDifference
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
open QuadraticGeometry
/-- The lower weighted kernel of an anisotropic plane with an arbitrary even radical has its exact Gaussian value. -/
theorem anisotropicPlaneKernel_weightedA (q m j : ℕ) (hq : 1<q) (hj : j≤m) :
    gaussianWeightedSum (q^2) (m+1) j (groupedRankKernelA (anisotropicPlaneKernel q (2*m)))=
      (q:ℚ)^((2*m+3)*j)*(gaussianPascal (q^2) m j:ℚ) := by
  have hQ : 1<q^2 := Nat.one_lt_pow (by omega) hq
  have hsum := rankOneMinusWeightedSum q (m+1) (m+1-j) hq (by omega) (by omega)
  have hjj : m+1-(m+1-j)=j := by omega
  rw [hjj,show m+1-1=m by omega,show 2*(m+1)+1=2*m+3 by omega] at hsum
  rw [←hsum]
  unfold gaussianWeightedSum
  apply Finset.sum_congr rfl
  intro u hu
  have huj : u≤j := by have := Finset.mem_range.mp hu; omega
  rw [anisotropicPlaneKernel_groupedA q m u hq (by omega),
    gaussianBinomial_eq_gaussianPascal _ _ _ hQ]
  have hs := gaussianPascal_symm (q^2) (m+1-u) (j-u) hQ (by omega)
  rw [show m+1-u-(j-u)=m+1-j by omega] at hs
  rw [hs]
/-- The upper weighted kernel of an anisotropic plane has the exact negative sign and normalization. -/
theorem anisotropicPlaneKernel_weightedB (q m j : ℕ) (hq : 1<q) (hj : j≤m) :
    gaussianWeightedSum (q^2) (m+1) j (groupedRankKernelB (anisotropicPlaneKernel q (2*m)))=
      -(q:ℚ)^((2*m+1)*(j+1))*(gaussianPascal (q^2) m j:ℚ) := by
  have hQ : 1<q^2 := Nat.one_lt_pow (by omega) hq
  have hblock : zeroEvenNewtonBlock q m=scaledGaussianNewtonBlock (q^2) m ((q:ℚ)^(2*m-1)) := by
    funext u
    unfold zeroEvenNewtonBlock scaledGaussianNewtonBlock
    push_cast
    rw [pow_mul]
  have hsum := gaussianPascal_weighted_backwardDifference (q^2) m j ((q:ℚ)^(2*m-1)) hQ hj
  calc
    _ = -(q:ℚ)^(2*m+1)*(∑ u ∈ Finset.range (j+1),
        (gaussianPascal (q^2) (m+1-u) (m+1-j):ℚ)*
          backwardDifference (scaledGaussianNewtonBlock (q^2) m ((q:ℚ)^(2*m-1))) u) := by
      unfold gaussianWeightedSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have huj : u≤j := by have := Finset.mem_range.mp hu; omega
      rw [anisotropicPlaneKernel_groupedB q m u hq (by omega),hblock,
        gaussianBinomial_eq_gaussianPascal _ _ _ hQ]
      have hs := gaussianPascal_symm (q^2) (m+1-u) (j-u) hQ (by omega)
      rw [show m+1-u-(j-u)=m+1-j by omega] at hs
      rw [hs]
      ring
    _ = _ := by
      rw [hsum]
      push_cast
      rw [←pow_mul,←pow_mul]
      have hex : (2*m+1)+2*j+(2*m-1)*j=(2*m+1)*(j+1) := by
        by_cases hm : m=0
        · subst m
          have hj0 : j=0 := by omega
          subst j
          norm_num
        · have hh : 2*m-1+1=2*m := by omega
          nlinarith
      calc
        _ = -((q:ℚ)^(2*m+1)*(q:ℚ)^(2*j)*(q:ℚ)^((2*m-1)*j))*
              (gaussianPascal (q^2) m j:ℚ) := by ring
        _ = _ := by rw [←pow_add,←pow_add,hex]
end BinaryFieldCounterexamples
