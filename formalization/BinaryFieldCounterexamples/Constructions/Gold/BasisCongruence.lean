/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicBasis
public import BinaryFieldCounterexamples.Constructions.Gold.TensorCongruence
public import Mathlib.LinearAlgebra.Matrix.Basis
/-!
# Basis independence of the actual alternating Fourier sums

The coordinate change between two bases and its explicit inverse induce the
literal tensor congruence. The dual coordinate change is its transpose, so the
matrix of the form reconstructs exactly in the new basis. The proved finite
congruence invariance then makes every actual rank-class character sum basis
independent, including when one basis is adapted to a hyperbolic splitting.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- The dual basis change is the transpose of the primal coordinate change. -/
theorem dualBasis_change_matrix {d : ℕ} (e e' : Module.Basis (Fin d) (ZMod 2) V) :
    e'.dualBasis.toMatrix e.dualBasis=(e.toMatrix e').transpose := by
  ext i j
  rw [Module.Basis.toMatrix_apply,e'.dualBasis_repr,e.dualBasis_apply,Matrix.transpose_apply]
  rfl
/-- Changing basis applies the literal invertible matrix congruence to the tensor. -/
theorem basisTensor_congruence
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) {d : ℕ}
    (e e' : Module.Basis (Fin d) (ZMod 2) V) :
    basisTensor C e'=tensorCongruence (e.toMatrix e') (basisTensor C e) := by
  apply tensorAlternatingMatrix_injective
  rw [tensorAlternatingMatrix_congruence,basisTensor_matrix C hs ha e,basisTensor_matrix C hs ha e',
    ←dualBasis_change_matrix]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e' e e'.dualBasis e.dualBasis C).symm
/-- Actual rank-class Fourier sums of a form are independent of the chosen basis. -/
theorem alternatingRankCharacterSum_basisTensor_eq
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) {d : ℕ}
    (e e' : Module.Basis (Fin d) (ZMod 2) V) (j : ℕ) :
    alternatingRankCharacterSum d j (basisTensor C e')=alternatingRankCharacterSum d j (basisTensor C e) := by
  rw [basisTensor_congruence C hs ha e e']
  exact alternatingRankCharacterSum_congruence (e.toMatrix e') (e'.toMatrix e)
    (e.toMatrix_mul_toMatrix_flip e') (e'.toMatrix_mul_toMatrix_flip e) j (basisTensor C e)
end BinaryFieldCounterexamples.Gold
