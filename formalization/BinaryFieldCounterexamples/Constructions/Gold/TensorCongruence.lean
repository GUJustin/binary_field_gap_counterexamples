/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.TensorBorder
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingFourier
/-!
# Invertible congruence and the actual alternating Fourier sums

Congruence acts on the literal upper-triangular tensor coordinates. Reconstructing
the alternating matrix proves composition and rank preservation; explicit inverse
matrices give an actual equivalence of the finite tensor set.

The character pairing sums each unordered edge exactly once. Its dual congruence
uses the transposed change matrix, as proved entrywise, and is not matrix trace
pairing. Reindexing the concrete rank-class sum by that dual equivalence proves
Fourier invariance under every invertible congruence.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
/-- The literal upper-coordinate tensor of an alternating-matrix congruence. -/
noncomputable def tensorCongruence {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : TensorIndex d → ZMod 2) : TensorIndex d → ZMod 2 := fun ij =>
  (P.transpose*tensorAlternatingMatrix A*P) ij.val.1 ij.val.2
/-- Entrywise expansion of congruence in the once-per-edge coordinates. -/
theorem tensorCongruence_matrix_apply {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : TensorIndex d → ZMod 2) (i j : Fin d) :
    (P.transpose*tensorAlternatingMatrix A*P) i j=
      ∑ kl : TensorIndex d, A kl*(P kl.val.1 i*P kl.val.2 j+P kl.val.2 i*P kl.val.1 j) := by
  classical
  simp only [Matrix.mul_apply,Matrix.transpose_apply,tensorAlternatingMatrix,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro kl hkl
  simp only [mul_add,add_mul,Finset.sum_add_distrib,mul_ite,ite_mul,mul_zero,zero_mul,mul_one]
  simp
  ring
/-- Congruence preserves the represented alternating matrix exactly. -/
theorem tensorAlternatingMatrix_congruence {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : TensorIndex d → ZMod 2) :
    tensorAlternatingMatrix (tensorCongruence P A)=P.transpose*tensorAlternatingMatrix A*P := by
  have hs (i j : Fin d) : (P.transpose*tensorAlternatingMatrix A*P) i j=
      (P.transpose*tensorAlternatingMatrix A*P) j i := by
    rw [tensorCongruence_matrix_apply,tensorCongruence_matrix_apply]
    apply Finset.sum_congr rfl
    intro kl hkl
    ring
  have hz (i : Fin d) : (P.transpose*tensorAlternatingMatrix A*P) i i=0 := by
    rw [tensorCongruence_matrix_apply]
    apply Finset.sum_eq_zero
    intro kl hkl
    have he : P kl.val.2 i*P kl.val.1 i=P kl.val.1 i*P kl.val.2 i := mul_comm _ _
    rw [he,CharTwo.add_self_eq_zero,mul_zero]
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [tensorAlternatingMatrix_apply_lt (tensorCongruence P A) hij]
    rfl
  · rw [tensorAlternatingMatrix_diagonal,hz]
  · have hsym := congrFun (congrFun (tensorAlternatingMatrix_transpose (tensorCongruence P A)).symm i) j
    rw [hsym,Matrix.transpose_apply,tensorAlternatingMatrix_apply_lt (tensorCongruence P A) hji]
    exact hs j i
/-- Successive congruences compose by the actual matrix product. -/
theorem tensorCongruence_comp {d : ℕ} (P Q : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : TensorIndex d → ZMod 2) :
    tensorCongruence Q (tensorCongruence P A)=tensorCongruence (P*Q) A := by
  apply tensorAlternatingMatrix_injective
  simp only [tensorAlternatingMatrix_congruence,Matrix.transpose_mul,Matrix.mul_assoc]
/-- Identity congruence fixes every tensor. -/
theorem tensorCongruence_one {d : ℕ} (A : TensorIndex d → ZMod 2) : tensorCongruence 1 A=A := by
  apply tensorAlternatingMatrix_injective
  simp [tensorAlternatingMatrix_congruence]
/-- Explicit inverse matrices induce an actual equivalence of tensor coordinates. -/
noncomputable def tensorCongruenceEquiv {d : ℕ} (P Q : Matrix (Fin d) (Fin d) (ZMod 2))
    (hPQ : P*Q=1) (hQP : Q*P=1) : (TensorIndex d → ZMod 2) ≃ (TensorIndex d → ZMod 2) :=
  { toFun := tensorCongruence P
    invFun := tensorCongruence Q
    left_inv := fun A => by rw [tensorCongruence_comp,hPQ,tensorCongruence_one]
    right_inv := fun A => by rw [tensorCongruence_comp,hQP,tensorCongruence_one] }
/-- Congruence can only decrease matrix rank without invertibility. -/
theorem tensorCongruence_rank_le {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : TensorIndex d → ZMod 2) :
    (tensorAlternatingMatrix (tensorCongruence P A)).rank≤(tensorAlternatingMatrix A).rank := by
  rw [tensorAlternatingMatrix_congruence]
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
/-- Invertible congruence preserves the literal tensor matrix rank. -/
theorem tensorCongruence_rank {d : ℕ} (P Q : Matrix (Fin d) (Fin d) (ZMod 2))
    (hPQ : P*Q=1) (A : TensorIndex d → ZMod 2) :
    (tensorAlternatingMatrix (tensorCongruence P A)).rank=(tensorAlternatingMatrix A).rank := by
  apply le_antisymm (tensorCongruence_rank_le P A)
  have hh := tensorCongruence_rank_le Q (tensorCongruence P A)
  rw [tensorCongruence_comp,hPQ,tensorCongruence_one] at hh
  exact hh
/-- Once-per-edge pairing makes transpose congruence the dual transformation. -/
theorem tensorCongruence_dotProduct {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2))
    (A B : TensorIndex d → ZMod 2) :
    dotProduct (tensorCongruence P A) B=dotProduct A (tensorCongruence P.transpose B) := by
  classical
  simp only [dotProduct,tensorCongruence,tensorCongruence_matrix_apply,
    Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro kl hkl
  ring
/-- The actual rank-class character sums are invariant under invertible congruence. -/
theorem alternatingRankCharacterSum_congruence {d : ℕ}
    (P Q : Matrix (Fin d) (Fin d) (ZMod 2)) (hPQ : P*Q=1) (hQP : Q*P=1)
    (j : ℕ) (A : TensorIndex d → ZMod 2) :
    alternatingRankCharacterSum d j (tensorCongruence P A)=alternatingRankCharacterSum d j A := by
  classical
  have htPQ : P.transpose*Q.transpose=1 := by rw [←Matrix.transpose_mul,hQP,Matrix.transpose_one]
  have htQP : Q.transpose*P.transpose=1 := by rw [←Matrix.transpose_mul,hPQ,Matrix.transpose_one]
  let e := tensorCongruenceEquiv P.transpose Q.transpose htPQ htQP
  have hr (B : TensorIndex d → ZMod 2) : (tensorAlternatingMatrix (e B)).rank=(tensorAlternatingMatrix B).rank :=
    tensorCongruence_rank P.transpose Q.transpose htPQ B
  have hd (B : TensorIndex d → ZMod 2) : dotProduct B (tensorCongruence P A)=dotProduct (e B) A := by
    rw [dotProduct_comm B (tensorCongruence P A),tensorCongruence_dotProduct,dotProduct_comm]
    rfl
  unfold alternatingRankCharacterSum
  calc
    _ = ∑ B : TensorIndex d → ZMod 2,
        if (tensorAlternatingMatrix (e B)).rank=2*j then BinaryQuadraticData.binarySign (dotProduct (e B) A) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hr,hd]
    _ = _ := Equiv.sum_comp e (fun B : TensorIndex d → ZMod 2 =>
      if (tensorAlternatingMatrix B).rank=2*j then BinaryQuadraticData.binarySign (dotProduct B A) else 0)
end BinaryFieldCounterexamples.Gold
