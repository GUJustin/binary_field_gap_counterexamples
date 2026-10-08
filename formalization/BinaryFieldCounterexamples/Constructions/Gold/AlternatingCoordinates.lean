/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
/-! # Alternating laws of the concrete tensor coordinate matrix -/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
/-- The coordinate matrix is symmetric in characteristic two. -/
theorem tensorAlternatingMatrix_transpose {d : ℕ} (A : TensorIndex d → ZMod 2) :
    (tensorAlternatingMatrix A).transpose=tensorAlternatingMatrix A := by
  ext i j
  simp only [Matrix.transpose_apply,tensorAlternatingMatrix]
  apply Finset.sum_congr rfl
  intro ij hij
  ring
/-- No diagonal coordinates occur in an alternating tensor. -/
theorem tensorAlternatingMatrix_diagonal {d : ℕ} (A : TensorIndex d → ZMod 2) (i : Fin d) :
    tensorAlternatingMatrix A i i=0 := by
  simp only [tensorAlternatingMatrix]
  apply Finset.sum_eq_zero
  intro ij hij
  have hne : ij.val.1 ≠ ij.val.2 := ne_of_lt ij.property
  by_cases h1 : ij.val.1=i <;> by_cases h2 : ij.val.2=i <;> simp_all
/-- The represented bilinear form vanishes on every diagonal pair. -/
theorem tensorAlternatingMatrix_alternating {d : ℕ} (A : TensorIndex d → ZMod 2)
    (x : Fin d → ZMod 2) : dotProduct x ((tensorAlternatingMatrix A).mulVec x)=0 := by
  classical
  simp only [dotProduct,Matrix.mulVec,tensorAlternatingMatrix]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  simp only [mul_add,add_mul,Finset.sum_add_distrib]
  simp only [Finset.mul_sum, mul_assoc]
  have hswap (f : Fin d → TensorIndex d → ZMod 2) :
      (∑ i, ∑ ij, f i ij) = ∑ ij, ∑ i, f i ij := Finset.sum_comm
  simp_rw [hswap]
  simp [ite_mul,mul_ite]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : x ij.val.2 * (A ij * x ij.val.1) = x ij.val.1 * (A ij * x ij.val.2) := by ring
  rw [he, CharTwo.add_self_eq_zero]
end BinaryFieldCounterexamples.Gold
