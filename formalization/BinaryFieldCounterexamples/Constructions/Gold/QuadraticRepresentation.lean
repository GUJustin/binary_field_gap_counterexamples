/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicBasis
public import BinaryFieldCounterexamples.Constructions.Gold.Family
/-!
# Every binary quadratic function has Gold coordinates

The polynomial coordinates used in the prose preceding Lemma 5.6 represent
every quadratic function vanishing at zero. The upper triangular tensor is
obtained from its polar form and the remaining difference is additive.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The prose before Lemma 5.6: the polar form of a quadratic Boolean function is symmetric. -/
theorem BinaryQuadraticData.polar_symmetric {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : BinaryQuadraticData V) (x y : V) : Q.polarMap x y = Q.polarMap y x := by
  have hxy := Q.map_add_polar x y
  have hyx := Q.map_add_polar y x
  rw [add_comm y x] at hyx
  linear_combination hxy - hyx
/-- The prose before Lemma 5.6: the polar form of a quadratic Boolean function is alternating. -/
theorem BinaryQuadraticData.polar_alternating {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : BinaryQuadraticData V) (x : V) : Q.polarMap x x = 0 := by
  have hx := Q.map_add_polar x x
  have hz : x+x=0 := by
    have he : (2 : ZMod 2) • x = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    simpa only [two_smul] using he
  rw [hz, Q.map_zero, CharTwo.add_self_eq_zero, zero_add] at hx
  exact hx.symm
/-- The prose before Lemma 5.6: the tensor extracted from a quadratic function has exactly its polar map. -/
theorem tensorPolarLinearMap_basisTensor (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (Q : BinaryQuadraticData D) :
    tensorPolarLinearMap D (basisParameter D e) (basisTensor Q.polarMap e) = Q.polarMap := by
  apply (LinearMap.toMatrix e e.dualBasis).injective
  rw [toMatrix_tensorPolarMap_basis D e (show TensorCoordinates d from basisTensor Q.polarMap e)]
  exact basisTensor_matrix Q.polarMap Q.polar_symmetric Q.polar_alternating e
/-- The prose before Lemma 5.6: every quadratic Boolean function vanishing at zero
 is `ψ_(A,ω)` for an actual alternating tensor and an actual label in the label space. -/
theorem exists_quadratic_gold_representation (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (Q : BinaryQuadraticData D) :
    ∃ (A : TensorCoordinates d) (ω : parameterDomain D),
      (∀ x : D, Q.toFun x = tensorQuadraticFunction D (basisParameter D e) A x +
        ((parameterEquiv D).symm ω) x) ∧
      tensorPolarLinearMap D (basisParameter D e) A = Q.polarMap := by
  let A : TensorCoordinates d := basisTensor Q.polarMap e
  have hpolar := tensorPolarLinearMap_basisTensor D e Q
  let l : D →+ ZMod 2 :=
    { toFun := fun x ↦ Q.toFun x + tensorQuadraticFunction D (basisParameter D e) A x
      map_zero' := by rw [Q.map_zero, tensorQuadraticFunction_zero, add_zero]
      map_add' := by
        intro x y
        rw [Q.map_add_polar, tensorQuadraticFunction_add]
        have he : tensorPolarMap D (basisParameter D e) A y x = Q.polarMap y x := by
          exact LinearMap.congr_fun (LinearMap.congr_fun hpolar y) x
        rw [he]
        linear_combination (norm := ring_nf) Q.polarMap y x * (CharTwo.two_eq_zero (R := ZMod 2)) }
  refine ⟨A, parameterEquiv D l, ?_, hpolar⟩
  intro x
  rw [AddEquiv.symm_apply_apply]
  change Q.toFun x = tensorQuadraticFunction D (basisParameter D e) A x +
    (Q.toFun x + tensorQuadraticFunction D (basisParameter D e) A x)
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
/-- The prose before Lemma 5.6: the Gold tensor and linear label are uniquely
 determined by their quadratic Boolean function in the chosen coordinates. -/
theorem quadratic_gold_representation_unique (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (A A' : TensorCoordinates d)
    (ω ω' : parameterDomain D)
    (h : ∀ x : D, tensorQuadraticFunction D (basisParameter D e) A x + ((parameterEquiv D).symm ω) x =
      tensorQuadraticFunction D (basisParameter D e) A' x + ((parameterEquiv D).symm ω') x) :
    A = A' ∧ ω = ω' := by
  have hp (x y : D) : tensorPolarMap D (basisParameter D e) A y x =
      tensorPolarMap D (basisParameter D e) A' y x := by
    have hxy := h (x+y)
    rw [tensorQuadraticFunction_add, tensorQuadraticFunction_add, map_add, map_add] at hxy
    linear_combination hxy - h x - h y
  have hA : A=A' := by
    funext ij
    have he := hp (e ij.val.1) (e ij.val.2)
    rw [tensorPolarMap_basis_entry, tensorPolarMap_basis_entry,
      tensorAlternatingMatrix_apply_lt A ij.property, tensorAlternatingMatrix_apply_lt A' ij.property] at he
    exact he
  refine ⟨hA, ?_⟩
  apply (parameterEquiv D).symm.injective
  ext x
  have hx := h x
  rw [hA] at hx
  exact add_left_cancel hx
/-- The prose before Lemma 5.6, assembled: every quadratic Boolean function
 vanishing at zero has exactly one pair `(A,ω)` of Gold coordinates. -/
theorem existsUnique_quadratic_gold_representation (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (Q : BinaryQuadraticData D) :
    ∃! p : TensorCoordinates d × parameterDomain D,
      ∀ x : D, Q.toFun x = tensorQuadraticFunction D (basisParameter D e) p.1 x +
        ((parameterEquiv D).symm p.2) x := by
  obtain ⟨A, ω, h, _⟩ := exists_quadratic_gold_representation D e Q
  refine ⟨(A,ω), h, ?_⟩
  intro p hp
  obtain ⟨hA, hω⟩ := quadratic_gold_representation_unique D e p.1 A p.2 ω (fun x ↦ (hp x).symm.trans (h x))
  exact Prod.ext hA hω
end BinaryFieldCounterexamples.Gold
