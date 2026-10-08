/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.BinaryFourier
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
public import Mathlib.LinearAlgebra.Matrix.Dual
/-!
# Concrete alternating-tensor Fourier sums

Characters pair the literal upper-triangular coordinates once per unordered
edge. Matrix trace pairing would vanish in characteristic two and is not used.
Each rank-class character sum is nonnegative after summing over any actual
binary linear code. The zero rank class consists exactly of the zero tensor,
so any nonnegative weighted combination has an explicit zero-class lower bound.
The Gaussian weighted character identity required by the population theorem is
still a separate proof obligation.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
open BinaryQuadraticData
attribute [local instance] Classical.propDecidable Classical.decEq
/-- The actual character sum over tensors of matrix rank `2j`. -/
noncomputable def alternatingRankCharacterSum (d j : ℕ)
    (A : TensorIndex d → ZMod 2) : ℤ :=
  ∑ B : TensorIndex d → ZMod 2,
    if (tensorAlternatingMatrix B).rank=2*j then binarySign (dotProduct B A) else 0

/-- Orthogonality makes every rank-class sum nonnegative on a linear code. -/
theorem sum_alternatingRankCharacterSum_nonneg (d j : ℕ)
    (C : Submodule (ZMod 2) (TensorIndex d → ZMod 2)) :
    0 ≤ ∑ A : C, alternatingRankCharacterSum d j A := by
  classical
  unfold alternatingRankCharacterSum
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro B hB
  by_cases h : (tensorAlternatingMatrix B).rank=2*j
  · simp only [h, ite_true]
    exact sum_binarySign_submodule_nonneg C ((dotProductEquiv (ZMod 2) (TensorIndex d)) B)
  · simp [h]

/-- A finite binary matrix has rank zero exactly when it is zero. -/
theorem matrix_rank_zero_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (ZMod 2)) : M.rank=0 ↔ M=0 := by
  constructor
  · intro h
    have hr : LinearMap.range M.mulVecLin=⊥ := by
      apply Submodule.finrank_eq_zero.mp
      exact h
    have hl : M.mulVecLin=0 := LinearMap.range_eq_bot.mp hr
    apply (Matrix.toLin' : Matrix n n (ZMod 2) ≃ₗ[ZMod 2] _).injective
    simpa [Matrix.toLin'_apply'] using hl
  · rintro rfl
    exact Matrix.rank_zero

/-- The zero tensor represents the zero alternating matrix. -/
theorem tensorAlternatingMatrix_zero (d : ℕ) :
    tensorAlternatingMatrix (fun _ : TensorIndex d => 0)=0 := by
  ext i j
  simp [tensorAlternatingMatrix]

/-- The rank-zero Fourier class is the single trivial character. -/
theorem alternatingRankCharacterSum_zero (d : ℕ)
    (A : TensorIndex d → ZMod 2) : alternatingRankCharacterSum d 0 A=1 := by
  classical
  have hz : ∀ B : TensorIndex d → ZMod 2,
      (tensorAlternatingMatrix B).rank=0 ↔ B=0 := by
    intro B
    rw [matrix_rank_zero_iff, ← tensorAlternatingMatrix_zero d]
    exact tensorAlternatingMatrix_injective.eq_iff
  simp [alternatingRankCharacterSum, hz]
/-- Retaining the rank-zero term bounds any nonnegative weighted rank sum. -/
theorem sum_weighted_alternating_characters_lower_bound
    (d s : ℕ) (w : ℕ → ℕ)
    (C : Submodule (ZMod 2) (TensorIndex d → ZMod 2)) :
    (Nat.card C : ℤ)*w 0 ≤
      ∑ A : C, ∑ j ∈ Finset.range (s+1),
        (w j : ℤ)*alternatingRankCharacterSum d j A := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (s+1)) =>
      mul_nonneg (Int.natCast_nonneg (w j))
        (sum_alternatingRankCharacterSum_nonneg d j C))
    (Finset.mem_range.mpr (by omega : 0<s+1))
  simpa [alternatingRankCharacterSum_zero, Nat.card_eq_fintype_card, mul_comm] using h
end BinaryFieldCounterexamples.Gold
