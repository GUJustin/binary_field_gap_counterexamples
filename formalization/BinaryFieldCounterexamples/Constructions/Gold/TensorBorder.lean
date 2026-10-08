/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingCoordinates
/-!
# Adding one coordinate to an alternating tensor

A tensor in dimension `d+1` splits bijectively and linearly into its old tensor
and its `d` new edge coordinates. This splitting preserves the literal character
pairing and identifies its matrix with the bordered block matrix, including rank.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
/-- Separate old unordered edges from the edges to the final coordinate. -/
noncomputable def tensorIndexBorderEquiv (d : ℕ) :
    TensorIndex (d+1) ≃ TensorIndex d ⊕ Fin d := by
  classical
  refine {
    toFun := fun ij => if h : ij.val.2.val<d then
      Sum.inl ⟨(⟨ij.val.1.val, by have := ij.property; exact lt_trans this h⟩,
        ⟨ij.val.2.val,h⟩),ij.property⟩
      else Sum.inr ⟨ij.val.1.val, by have := ij.property; have := ij.val.2.isLt; omega⟩
    invFun := fun z => match z with
      | Sum.inl ij => ⟨(ij.val.1.castSucc,ij.val.2.castSucc),ij.property⟩
      | Sum.inr i => ⟨(i.castSucc,Fin.last d),by exact i.isLt⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro ij
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        have := ij.val.2.isLt
        simp only [Fin.val_last]
        omega
  · intro z
    rcases z with ij | i
    · simp only [Fin.val_castSucc, dite_eq_left ij.val.2.isLt]
    · simp
/-- The exact linear decomposition into old tensor and border vector. -/
noncomputable def tensorBorderEquiv (d : ℕ) :
    (TensorIndex (d+1) → ZMod 2) ≃ₗ[ZMod 2]
      (TensorIndex d → ZMod 2) × (Fin d → ZMod 2) :=
  (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : TensorIndex (d+1) => ZMod 2)
    (tensorIndexBorderEquiv d)).trans
    (LinearEquiv.sumArrowLequivProdArrow (TensorIndex d) (Fin d) (ZMod 2) (ZMod 2))

/-- The old tensor retains every original edge coordinate. -/
theorem tensorBorderEquiv_fst (d : ℕ) (A : TensorIndex (d+1) → ZMod 2)
    (ij : TensorIndex d) :
    (tensorBorderEquiv d A).1 ij = A ⟨(ij.val.1.castSucc,ij.val.2.castSucc),ij.property⟩ := by
  rfl

/-- The border vector is the literal set of edges to the final coordinate. -/
theorem tensorBorderEquiv_snd (d : ℕ) (A : TensorIndex (d+1) → ZMod 2)
    (i : Fin d) :
    (tensorBorderEquiv d A).2 i = A ⟨(i.castSucc,Fin.last d),i.isLt⟩ := by
  rfl

/-- The upper-coordinate character pairing splits into its two components. -/
theorem tensorBorder_dotProduct (d : ℕ) (A B : TensorIndex (d+1) → ZMod 2) :
    dotProduct A B = dotProduct (tensorBorderEquiv d A).1 (tensorBorderEquiv d B).1 +
      dotProduct (tensorBorderEquiv d A).2 (tensorBorderEquiv d B).2 := by
  classical
  unfold dotProduct
  rw [← Equiv.sum_comp (tensorIndexBorderEquiv d).symm]
  rw [Fintype.sum_sum_type]
  rfl
/-- The old matrix block is unchanged under the tensor decomposition. -/
theorem tensorBorder_matrix_old (d : ℕ) (A : TensorIndex (d+1) → ZMod 2)
    (i j : Fin d) :
    tensorAlternatingMatrix A i.castSucc j.castSucc =
      tensorAlternatingMatrix (tensorBorderEquiv d A).1 i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [tensorAlternatingMatrix_apply_lt A hij,
      tensorAlternatingMatrix_apply_lt ((tensorBorderEquiv d A).1) hij, tensorBorderEquiv_fst]
  · rw [tensorAlternatingMatrix_diagonal, tensorAlternatingMatrix_diagonal]
  · have hs (n : ℕ) (C : TensorIndex n → ZMod 2) (a b : Fin n) :
        tensorAlternatingMatrix C a b=tensorAlternatingMatrix C b a := by
      exact congrFun (congrFun (tensorAlternatingMatrix_transpose C).symm a) b
    rw [hs _ A i.castSucc j.castSucc, hs _ (tensorBorderEquiv d A).1 i j,
      tensorAlternatingMatrix_apply_lt A hji,
      tensorAlternatingMatrix_apply_lt ((tensorBorderEquiv d A).1) hji, tensorBorderEquiv_fst]

/-- The new final column contains exactly the border vector. -/
theorem tensorBorder_matrix_last (d : ℕ) (A : TensorIndex (d+1) → ZMod 2)
    (i : Fin d) :
    tensorAlternatingMatrix A i.castSucc (Fin.last d)=(tensorBorderEquiv d A).2 i := by
  rw [tensorAlternatingMatrix_apply_lt A (show i.castSucc<Fin.last d from i.isLt),
    tensorBorderEquiv_snd]
/-- Identify the old coordinates and one final coordinate with `Fin (d+1)`. -/
def finBorderEquiv (d : ℕ) : Fin d ⊕ Unit ≃ Fin (d+1) := by
  refine {
    toFun := Sum.elim Fin.castSucc (fun _ => Fin.last d)
    invFun := fun i => if h : i.val<d then Sum.inl ⟨i.val,h⟩ else Sum.inr ()
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    rcases z with i | u
    · simp [i.isLt]
    · cases u
      simp
  · intro i
    dsimp only
    split_ifs with h
    · rfl
    · apply Fin.ext
      have := i.isLt
      change d=i.val
      omega

/-- The concrete matrix is exactly the bordered block matrix after reindexing. -/
theorem tensorBorder_matrix_blocks (d : ℕ) (A : TensorIndex (d+1) → ZMod 2) :
    (tensorAlternatingMatrix A).submatrix (finBorderEquiv d) (finBorderEquiv d) =
      Matrix.fromBlocks (tensorAlternatingMatrix (tensorBorderEquiv d A).1)
        (fun i (_ : Unit) => (tensorBorderEquiv d A).2 i)
        (fun (_ : Unit) j => (tensorBorderEquiv d A).2 j) 0 := by
  ext i j
  rcases i with i | u <;> rcases j with j | v
  · exact tensorBorder_matrix_old d A i j
  · exact tensorBorder_matrix_last d A i
  · change tensorAlternatingMatrix A (Fin.last d) j.castSucc = _
    have hs := congrFun (congrFun (tensorAlternatingMatrix_transpose A) j.castSucc) (Fin.last d)
    exact hs.trans (tensorBorder_matrix_last d A j)
  · exact tensorAlternatingMatrix_diagonal A (Fin.last d)
/-- The concrete tensor rank equals the rank of its bordered matrix. -/
theorem tensorBorder_matrix_rank (d : ℕ) (A : TensorIndex (d+1) → ZMod 2) :
    (tensorAlternatingMatrix A).rank =
      (Matrix.fromBlocks (tensorAlternatingMatrix (tensorBorderEquiv d A).1)
        (fun i (_ : Unit) => (tensorBorderEquiv d A).2 i)
        (fun (_ : Unit) j => (tensorBorderEquiv d A).2 j) 0).rank := by
  rw [← tensorBorder_matrix_blocks, Matrix.rank_submatrix]
end BinaryFieldCounterexamples.Gold
