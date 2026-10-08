/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.QuadraticWeightedChains
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Boundary cancellation and zero tails for quadratic kernels

The nonzero rank-one and anisotropic bases have a final grouped term at the
ambient half-dimension.  This term cancels the telescoping lower groups.
Together with the already proved support tails, this extends every weighted
kernel evaluation to all weight indices in the ambient range.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
open QuadraticGeometry

theorem rankOneIncidenceKernel_top (q b : ℕ) (hq : 1 < q) (hb : 0 < b) :
    rankOneIncidenceKernel q b (2*b) = 0 := by
  rw [rankOneIncidenceKernel, gaussianPascal_eq_zero q (2*b-1) (2*b) (by omega),
    show 2*b=(2*b-1)+1 by omega, gaussianMobiusParityLowerSum_succ q (2*b-1)]
  simp only [Nat.cast_zero, zero_mul, zero_add, gaussianPascal_self, Nat.cast_one,
    one_mul]
  rw [show 2*b-1=2*(b-1)+1 by omega, gaussianMobiusParitySum_odd q (b-1) hq]
  ring

theorem rankOneIncidenceKernel_top_succ (q b : ℕ) (hb : 0 < b) :
    rankOneIncidenceKernel q b (2*b+1) = 0 := by
  rw [rankOneIncidenceKernel,
    gaussianPascal_eq_zero q (2*b-1) (2*b+1) (by omega),
    gaussianPascal_eq_zero q (2*b-1) (2*b+1-1) (by omega)]
  ring

theorem rankOneGroupedKernelA_boundary (q b : ℕ) (hq : 1 < q) (hb : 0 < b) :
    groupedRankKernelA (rankOneIncidenceKernel q b) b =
      -rankOneNewtonBlock q b (b-1) := by
  rw [show b=(b-1)+1 by omega]
  simp only [groupedRankKernelA]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ b)]
  rw [show 2*(b-1)+2=2*b by omega,
    show 2*(b-1)+1=2*b-1 by omega]
  rw [rankOneIncidenceKernel_top q b hq hb]
  rw [show 2*b-1=2*(b-1)+1 by omega,
    rankOneIncidenceKernel_odd q b (b-1) hq (by omega)]
  ring

theorem rankOneIncidenceKernel_weighted_boundary (q b : ℕ)
    (hq : 1 < q) (hb : 0 < b) :
    gaussianWeightedSum (q^2) b b
      (groupedRankKernelA (rankOneIncidenceKernel q b)) = 0 := by
  unfold gaussianWeightedSum
  have hw (u : ℕ) (hu : u ≤ b) : gaussianBinomial (q^2) (b-u) (b-u)=1 := by
    rw [gaussianBinomial_eq_gaussianPascal (q^2) (b-u) (b-u)
      (Nat.one_lt_pow (by omega) hq), gaussianPascal_self]
  calc
    (∑ u ∈ Finset.range (b+1),
        (gaussianBinomial (q^2) (b-u) (b-u) : ℚ) *
          groupedRankKernelA (rankOneIncidenceKernel q b) u) =
      ∑ u ∈ Finset.range (b+1), groupedRankKernelA (rankOneIncidenceKernel q b) u := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hw u (by simpa using Finset.mem_range.mp hu)]
        norm_num
    _ = 0 := by
      rw [Finset.sum_range_succ,
        rankOneGroupedKernelA_boundary q b hq hb]
      have hs := sum_backwardDifference (b-1) (fun _ => (1 : ℚ))
        (rankOneNewtonBlock q b)
      simp only [one_mul, sub_self, zero_mul, Finset.sum_const_zero, zero_add] at hs
      rw [show b-1+1=b by omega] at hs
      have hsum :
          (∑ x ∈ Finset.range b, groupedRankKernelA (rankOneIncidenceKernel q b) x) =
          ∑ x ∈ Finset.range b, backwardDifference (rankOneNewtonBlock q b) x := by
        apply Finset.sum_congr rfl
        intro u hu
        have hg : groupedRankKernelA (rankOneIncidenceKernel q b) u =
            rankOneGroupedKernelA q b u := by cases u <;> rfl
        rw [hg]
        exact rankOneGroupedKernelA_eq q b u hq (by
          have := Finset.mem_range.mp hu
          omega)
      rw [hsum, hs]
      ring

theorem rankOneIncidenceKernel_weightedB_boundary (q b : ℕ)
    (hq : 1 < q) (hb : 0 < b) :
    gaussianWeightedSum (q^2) b b
      (groupedRankKernelB (rankOneIncidenceKernel q b)) = 0 := by
  unfold gaussianWeightedSum
  apply Finset.sum_eq_zero
  intro u hu
  have hub : u ≤ b := by simpa using Finset.mem_range.mp hu
  by_cases hult : u < b
  · change (gaussianBinomial (q^2) (b-u) (b-u) : ℚ) *
      rankOneGroupedKernelB q b u = 0
    rw [rankOneGroupedKernelB_eq_zero q b u hq (by omega)]
    ring
  · have hu_eq : u=b := by omega
    subst u
    unfold groupedRankKernelB
    rw [rankOneIncidenceKernel_top q b hq hb,
      rankOneIncidenceKernel_top_succ q b hb]
    ring

theorem anisotropicPlaneKernel_top (q m : ℕ) (hq : 1 < q) :
    anisotropicPlaneKernel q (2*m) (2*m+2) =
      (q : ℚ)^(2*m+1) * zeroEvenNewtonBlock q m m := by
  rw [anisotropicPlaneKernel_three_term q (2*m) (2*m) hq,
    gaussianPascal_eq_zero q (2*m) (2*m+2) (by omega),
    gaussianPascal_eq_zero q (2*m) (2*m+1) (by omega),
    gaussianPascal_self, gaussianMobiusTwiceSum_even q m hq]
  have hz := zeroEvenBlock_eq_newton q m m hq (by omega)
  rw [zeroEvenBlock, gaussianPascal_self, symmetricParitySum_even_product q m hq] at hz
  norm_num at hz ⊢
  rw [← hz, pow_succ]
  ring

theorem anisotropicPlaneKernel_top_succ (q m : ℕ) (hq : 1 < q) :
    anisotropicPlaneKernel q (2*m) (2*m+3) = 0 := by
  rw [show 2*m+3=(2*m+1)+2 by omega,
    anisotropicPlaneKernel_three_term q (2*m) (2*m+1) hq,
    gaussianPascal_eq_zero q (2*m) (2*m+3) (by omega),
    gaussianPascal_eq_zero q (2*m) (2*m+2) (by omega),
    gaussianPascal_eq_zero q (2*m) (2*m+1) (by omega)]
  ring

theorem anisotropicPlaneKernel_groupedA_boundary (q m : ℕ) (hq : 1 < q) :
    groupedRankKernelA (anisotropicPlaneKernel q (2*m)) (m+1) =
      -rankOneNewtonBlock q (m+1) m := by
  simp only [groupedRankKernelA]
  rw [anisotropicPlaneKernel_pair_odd q (2*m) m hq]
  rw [gaussianPascal_eq_zero q (2*m+1) (2*(m+1)) (by omega)]
  norm_num only [Nat.cast_zero, zero_mul, zero_sub]
  rw [← rankOneMobiusBlock_eq_newton q (m+1) m hq (by omega)]
  unfold rankOneMobiusBlock
  rw [show 2*(m+1)-1=2*m+1 by omega]

theorem anisotropicPlaneKernel_groupedB_boundary (q m : ℕ) (hq : 1 < q) :
    groupedRankKernelB (anisotropicPlaneKernel q (2*m)) (m+1) =
      (q : ℚ)^(2*m+1) * zeroEvenNewtonBlock q m m := by
  unfold groupedRankKernelB
  rw [show 2*(m+1)=2*m+2 by omega, show 2*m+2+1=2*m+3 by omega,
    anisotropicPlaneKernel_top q m hq, anisotropicPlaneKernel_top_succ q m hq]
  ring

theorem anisotropicPlaneKernel_weightedA_boundary (q m : ℕ) (hq : 1 < q) :
    gaussianWeightedSum (q^2) (m+1) (m+1)
      (groupedRankKernelA (anisotropicPlaneKernel q (2*m))) = 0 := by
  unfold gaussianWeightedSum
  have hw (u : ℕ) (hu : u ≤ m+1) :
      gaussianBinomial (q^2) (m+1-u) (m+1-u)=1 := by
    rw [gaussianBinomial_eq_gaussianPascal (q^2) (m+1-u) (m+1-u)
      (Nat.one_lt_pow (by omega) hq), gaussianPascal_self]
  calc
    (∑ u ∈ Finset.range (m+1+1),
        (gaussianBinomial (q^2) (m+1-u) (m+1-u) : ℚ) *
          groupedRankKernelA (anisotropicPlaneKernel q (2*m)) u) =
      ∑ u ∈ Finset.range (m+1+1),
        groupedRankKernelA (anisotropicPlaneKernel q (2*m)) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hw u (by simpa using Finset.mem_range.mp hu)]
          norm_num
    _ = 0 := by
      rw [Finset.sum_range_succ,
        anisotropicPlaneKernel_groupedA_boundary q m hq]
      have hs := sum_backwardDifference m (fun _ => (1 : ℚ))
        (rankOneNewtonBlock q (m+1))
      simp only [one_mul, sub_self, zero_mul, Finset.sum_const_zero, zero_add] at hs
      have hsum :
          (∑ u ∈ Finset.range (m+1), groupedRankKernelA
            (anisotropicPlaneKernel q (2*m)) u) =
          ∑ u ∈ Finset.range (m+1), backwardDifference
            (rankOneNewtonBlock q (m+1)) u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact anisotropicPlaneKernel_groupedA q m u hq (by
          have := Finset.mem_range.mp hu
          omega)
      rw [hsum, hs]
      ring

theorem anisotropicPlaneKernel_weightedB_boundary (q m : ℕ) (hq : 1 < q) :
    gaussianWeightedSum (q^2) (m+1) (m+1)
      (groupedRankKernelB (anisotropicPlaneKernel q (2*m))) = 0 := by
  unfold gaussianWeightedSum
  have hw (u : ℕ) (hu : u ≤ m+1) :
      gaussianBinomial (q^2) (m+1-u) (m+1-u)=1 := by
    rw [gaussianBinomial_eq_gaussianPascal (q^2) (m+1-u) (m+1-u)
      (Nat.one_lt_pow (by omega) hq), gaussianPascal_self]
  calc
    (∑ u ∈ Finset.range (m+1+1),
        (gaussianBinomial (q^2) (m+1-u) (m+1-u) : ℚ) *
          groupedRankKernelB (anisotropicPlaneKernel q (2*m)) u) =
      ∑ u ∈ Finset.range (m+1+1),
        groupedRankKernelB (anisotropicPlaneKernel q (2*m)) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hw u (by simpa using Finset.mem_range.mp hu)]
          norm_num
    _ = 0 := by
      rw [Finset.sum_range_succ,
        anisotropicPlaneKernel_groupedB_boundary q m hq]
      have hs := sum_backwardDifference m (fun _ => (1 : ℚ))
        (zeroEvenNewtonBlock q m)
      simp only [one_mul, sub_self, zero_mul, Finset.sum_const_zero, zero_add] at hs
      have hsum :
          (∑ u ∈ Finset.range (m+1), groupedRankKernelB
            (anisotropicPlaneKernel q (2*m)) u) =
          -(q : ℚ)^(2*m+1) *
            ∑ u ∈ Finset.range (m+1), backwardDifference
              (zeroEvenNewtonBlock q m) u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [anisotropicPlaneKernel_groupedB q m u hq (by
          have := Finset.mem_range.mp hu
          omega)]
      rw [hsum, hs]
      ring

/-- The positive-even lower evaluation, including its Gaussian zero range. -/
theorem positiveEvenKernelChain_weightedA_all (q n s j : ℕ) (hq : 1 < q)
    (hsn : s ≤ n) (hj : j ≤ n) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = zeroQuadraticKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelA (K s)) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s) j : ℚ) := by
  by_cases hjb : j ≤ n-s
  · exact positiveEvenKernelChain_weightedA q n s j hq hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedA q (n-s) s j hq K hK (by omega)]
    rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s) j
      (groupedRankKernelA (K 0)) (by omega) (hK.2.2.2.1 0),
      gaussianPascal_eq_zero (q^2) (n-s) j (by omega)]
    ring

/-- The positive-even upper evaluation, including its Gaussian zero range. -/
theorem positiveEvenKernelChain_weightedB_all (q n s j : ℕ) (hq : 1 < q)
    (hsn : s ≤ n) (hj : j ≤ n) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = zeroQuadraticKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelB (K s)) =
      (q : ℚ)^((2*n-1)*j+2*n-s) *
        (gaussianPascal (q^2) (n-s) j : ℚ) := by
  by_cases hjb : j ≤ n-s
  · exact positiveEvenKernelChain_weightedB q n s j hq hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedB q (n-s) s j hq K hK (by omega)]
    rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s) j
      (groupedRankKernelB (K 0)) (by omega) (hK.2.2.2.2 0),
      gaussianPascal_eq_zero (q^2) (n-s) j (by omega)]
    ring

/-- The odd lower evaluation, with boundary cancellation and all zero tails. -/
theorem oddKernelChain_weightedA_all (q n s j : ℕ) (hq : 1 < q)
    (hsn : s < n) (hj : j ≤ n) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = rankOneIncidenceKernel q (n-s)) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelA (K s)) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s-1) j : ℚ) := by
  by_cases hjb : j < n-s
  · exact oddKernelChain_weightedA q n s j hq hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedA q (n-s) s j hq K hK (by omega), hbase]
    by_cases heq : j=n-s
    · subst j
      rw [rankOneIncidenceKernel_weighted_boundary q (n-s) hq (by omega),
        gaussianPascal_eq_zero (q^2) (n-s-1) (n-s) (by omega)]
      ring
    · rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s) j
        (groupedRankKernelA (rankOneIncidenceKernel q (n-s))) (by omega)
        (by simpa [hbase] using hK.2.2.2.1 0),
        gaussianPascal_eq_zero (q^2) (n-s-1) j (by omega)]
      ring

/-- The odd upper evaluation vanishes for every weight index. -/
theorem oddKernelChain_weightedB_all (q n s j : ℕ) (hq : 1 < q)
    (hsn : s < n) (hj : j ≤ n) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = rankOneIncidenceKernel q (n-s)) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelB (K s)) = 0 := by
  by_cases hjb : j < n-s
  · exact oddKernelChain_weightedB q n s j hq hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedB q (n-s) s j hq K hK (by omega), hbase]
    by_cases heq : j=n-s
    · subst j
      rw [rankOneIncidenceKernel_weightedB_boundary q (n-s) hq (by omega)]
      ring
    · rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s) j
        (groupedRankKernelB (rankOneIncidenceKernel q (n-s))) (by omega)
        (by simpa [hbase] using hK.2.2.2.2 0)]
      ring

/-- The negative-even lower evaluation, including boundary cancellation. -/
theorem negativeEvenKernelChain_weightedA_all (q n s j : ℕ) (hq : 1 < q)
    (hs0 : 0 < s) (hsn : s ≤ n) (hj : j ≤ n)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q (n-s+1) K)
    (hbase : K 0 = anisotropicPlaneKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s+1)+(s-1)) j
        (groupedRankKernelA (K (s-1))) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s) j : ℚ) := by
  by_cases hjb : j ≤ n-s
  · exact negativeEvenKernelChain_weightedA q n s j hq hs0 hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedA q (n-s+1) (s-1) j hq K hK (by omega), hbase]
    by_cases heq : j=n-s+1
    · subst j
      rw [anisotropicPlaneKernel_weightedA_boundary q (n-s) hq,
        gaussianPascal_eq_zero (q^2) (n-s) (n-s+1) (by omega)]
      ring
    · rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s+1) j
        (groupedRankKernelA (anisotropicPlaneKernel q (2*(n-s)))) (by omega)
        (by simpa [hbase] using hK.2.2.2.1 0),
        gaussianPascal_eq_zero (q^2) (n-s) j (by omega)]
      ring

/-- The negative-even upper evaluation, including boundary cancellation. -/
theorem negativeEvenKernelChain_weightedB_all (q n s j : ℕ) (hq : 1 < q)
    (hs0 : 0 < s) (hsn : s ≤ n) (hj : j ≤ n)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q (n-s+1) K)
    (hbase : K 0 = anisotropicPlaneKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s+1)+(s-1)) j
        (groupedRankKernelB (K (s-1))) =
      -(q : ℚ)^((2*n-1)*j+2*n-s) *
        (gaussianPascal (q^2) (n-s) j : ℚ) := by
  by_cases hjb : j ≤ n-s
  · exact negativeEvenKernelChain_weightedB q n s j hq hs0 hsn hjb K hK hbase
  · rw [hyperbolicKernelChain_weightedB q (n-s+1) (s-1) j hq K hK (by omega), hbase]
    by_cases heq : j=n-s+1
    · subst j
      rw [anisotropicPlaneKernel_weightedB_boundary q (n-s) hq,
        gaussianPascal_eq_zero (q^2) (n-s) (n-s+1) (by omega)]
      ring
    · rw [gaussianWeightedSum_eq_zero_of_tail (q^2) (n-s+1) j
        (groupedRankKernelB (anisotropicPlaneKernel q (2*(n-s)))) (by omega)
        (by simpa [hbase] using hK.2.2.2.2 0),
        gaussianPascal_eq_zero (q^2) (n-s) j (by omega)]
      ring

end BinaryFieldCounterexamples
