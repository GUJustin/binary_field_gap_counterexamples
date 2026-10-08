/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualWeightedInduction
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RankCharacterKernel

/-!
# Literal quadratic character moments

Finite symmetric-matrix character sums regroup by exact rank.  At the
complementary Gaussian index, the ceiling-rank weight is exactly the lower
grouped inverse-kernel moment evaluated by the actual quadratic induction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
open QuadraticGeometry

theorem sum_range_pair_ranks {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    (∑ r ∈ Finset.range (2*n+1), f r) =
      f 0 + ∑ u ∈ Finset.range n, (f (2*u+1)+f (2*u+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      abel

/-- At complementary indices, the truncated Gaussian weighted sum equals its
full ambient-range version because every omitted Gaussian coefficient is zero. -/
theorem gaussianWeightedSum_complementary_full (Q n t : ℕ) (hQ : 1 < Q)
    (htn : t ≤ n) (P : ℕ → ℚ) :
    gaussianWeightedSum Q n (n-t) P =
      ∑ u ∈ Finset.range (n+1), (gaussianPascal Q (n-u) t : ℚ) * P u := by
  let j := n-t
  have hsplit : n+1=(j+1)+t := by dsimp [j]; omega
  rw [hsplit, Finset.sum_range_add]
  have htail : (∑ a ∈ Finset.range t,
      (gaussianPascal Q (n-(j+1+a)) t : ℚ) * P (j+1+a))=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hat : a<t := Finset.mem_range.mp ha
    rw [gaussianPascal_eq_zero Q (n-(j+1+a)) t (by dsimp [j]; omega)]
    ring
  rw [htail, add_zero]
  unfold gaussianWeightedSum
  apply Finset.sum_congr rfl
  intro u hu
  have huj : u ≤ j := by simpa using Finset.mem_range.mp hu
  rw [gaussianBinomial_eq_gaussianPascal Q (n-u) (j-u) hQ]
  have hs := gaussianPascal_symm Q (n-u) (j-u) hQ (by dsimp [j]; omega)
  rw [show n-u-(j-u)=t by dsimp [j]; omega] at hs
  rw [hs]

/-- The ceiling-rank raw kernel moment is exactly the lower grouped Gaussian
moment. -/
theorem quadraticMinusRankWeight_kernel_sum (q n t : ℕ) (hq : 1 < q)
    (htn : t ≤ n) (K : ℕ → ℚ) :
    (∑ r ∈ Finset.range (2*n+1), quadraticMinusRankWeight q n t r * K r) =
      gaussianWeightedSum (q^2) n (n-t) (groupedRankKernelA K) := by
  rw [gaussianWeightedSum_complementary_full (q^2) n t
    (Nat.one_lt_pow (by omega) hq) htn]
  rw [sum_range_pair_ranks n (fun r => quadraticMinusRankWeight q n t r*K r)]
  unfold quadraticMinusRankWeight
  norm_num only [zero_add, Nat.reduceDiv, Nat.sub_zero]
  conv_rhs => rw [Finset.sum_range_succ', add_comm]
  apply congrArg (fun z : ℚ => (gaussianPascal (q^2) n t : ℚ)*K 0+z)
  apply Finset.sum_congr rfl
  intro u hu
  have hun : u<n := Finset.mem_range.mp hu
  simp only [groupedRankKernelA]
  rw [show (2*u+1+1)/2=u+1 by omega,
    show (2*u+2+1)/2=u+1 by omega]
  ring

end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open QuadraticGeometry
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype

/-- Regroup a literal symmetric-matrix character sum by exact matrix rank. -/
theorem weighted_symmetric_character_sum_eq_rankKernels
    {k : Type*} [Field k] [Fintype k] (d : ℕ) (w : ℕ → ℚ)
    (psi : AddChar k ℂ) (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (w M.val.rank : ℂ) * psi (matrixPairing d Q M)) =
      ∑ r ∈ Finset.range (d+1), (w r : ℂ) * rankCharacterKernel d psi Q r := by
  unfold rankCharacterKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M hM
  have hr : M.val.rank ∈ Finset.range (d+1) := by
    simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (by simpa using M.val.rank_le_card_width)
  rw [Finset.sum_eq_single M.val.rank]
  · simp
  · intro r hrange hrne
    rw [ite_eq_right (Ne.symm hrne)]
    ring
  · intro hnot
    exact (hnot hr).elim

/-- The literal ceiling-rank matrix character moment is the rational grouped
kernel moment evaluated by `actual_weightedKernelA`. -/
theorem quadraticMinusRankWeight_characterSum_eq_weightedKernel
    {k : Type*} [Field k] [Fintype k] (n t : ℕ) (htn : t ≤ n)
    (psi : AddChar k ℂ) (hpsi : psi≠1) (Q : QuadraticForm k (Fin (2*n) → k)) :
    (∑ M : symmetricMatrices (k:=k) (2*n),
      (quadraticMinusRankWeight (Fintype.card k) n t M.val.rank : ℂ) *
        psi (matrixPairing (2*n) Q M)) =
      (gaussianWeightedSum ((Fintype.card k)^2) n (n-t)
        (groupedRankKernelA (quadraticRankKernel Q)) : ℂ) := by
  rw [weighted_symmetric_character_sum_eq_rankKernels]
  simp_rw [rankCharacterKernel_eq_inverse (2*n) _ psi hpsi Q]
  simp_rw [← Rat.cast_mul]
  norm_cast
  simpa [quadraticRankKernel] using
    (quadraticMinusRankWeight_kernel_sum (Fintype.card k) n t
      Fintype.one_lt_card htn (quadraticRankKernel Q))

end BinaryFieldCounterexamples.QuadraticCoordinates
