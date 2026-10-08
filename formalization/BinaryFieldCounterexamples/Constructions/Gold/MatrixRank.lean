/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.Polar
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Coordinate matrices for Gold polar forms
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

open scoped BigOperators

variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- The Gold parameter corresponding to a coordinate functional of a basis of
`D`. -/
noncomputable def basisParameter (D : AddSubgroup B) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (i : Fin d) : parameterDomain D :=
  parameterEquiv D (e.coord i).toAddMonoidHom

/-- Basis parameters and basis vectors are exactly dual. -/
theorem basisParameter_eval (D : AddSubgroup B) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (i j : Fin d) :
    ((parameterEquiv D).symm (basisParameter D e i)) (e j) =
      if i = j then 1 else 0 := by
  rw [basisParameter, AddEquiv.symm_apply_apply]
  change e.repr (e j) i = _
  simpa [eq_comm] using e.repr_self_apply j i

/-- The tensor polar map with its additive functionals reinterpreted as
binary-linear functionals. -/
noncomputable def tensorPolarLinearMap (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    D →ₗ[ZMod 2] Module.Dual (ZMod 2) D :=
  { toFun := fun y ↦ (tensorPolarFunctional D v A y).toZModLinearMap 2
    map_add' := by
      intro y z
      ext x
      change tensorPolarMap D v A (y + z) x =
        tensorPolarMap D v A y x + tensorPolarMap D v A z x
      rw [map_add]
      rfl
    map_smul' := by
      intro c y
      ext x
      change tensorPolarMap D v A (c • y) x = c * tensorPolarMap D v A y x
      rw [map_smul]
      rfl }

/-- Reinterpreting the values of the tensor polar map does not change its
intrinsic rank. -/
theorem tensorPolarLinearMap_finrank_range (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Module.finrank (ZMod 2) (LinearMap.range (tensorPolarLinearMap D v A)) =
      tensorPolarRank D v A := by
  have hk : LinearMap.ker (tensorPolarLinearMap D v A) =
      LinearMap.ker (tensorPolarMap D v A) := by
    ext y
    change (tensorPolarLinearMap D v A y = 0) ↔ (tensorPolarMap D v A y = 0)
    constructor
    · intro h
      apply AddMonoidHom.ext
      intro x
      have hx := DFunLike.congr_fun h x
      simpa [tensorPolarLinearMap, tensorPolarMap] using hx
    · intro h
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun h x
      simpa [tensorPolarLinearMap, tensorPolarMap] using hx
  have hnew := (tensorPolarLinearMap D v A).finrank_range_add_finrank_ker
  have hold := (tensorPolarMap D v A).finrank_range_add_finrank_ker
  unfold tensorPolarRank
  rw [hk] at hnew
  omega

/-- The symmetric zero-diagonal coordinate matrix represented by the strict
upper-triangular tensor coordinates. -/
def tensorAlternatingMatrix {d : ℕ} (A : TensorCoordinates d) :
    Matrix (Fin d) (Fin d) (ZMod 2) := fun i j ↦
  ∑ ij : TensorIndex d, A ij *
    ((if ij.val.1 = j then 1 else 0) * (if ij.val.2 = i then 1 else 0) +
      (if ij.val.2 = j then 1 else 0) * (if ij.val.1 = i then 1 else 0))

/-- Coordinate entries of the actual polar map are the alternating tensor
matrix entries. -/
theorem tensorPolarMap_basis_entry (D : AddSubgroup B) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (A : TensorCoordinates d) (i j : Fin d) :
    tensorPolarMap D (basisParameter D e) A (e j) (e i) =
      tensorAlternatingMatrix A i j := by
  change tensorPolarFunctional D (basisParameter D e) A (e j) (e i) = _
  simp only [tensorPolarFunctional, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    basisParameter_eval]
  rfl

/-- The intrinsic polar map in the basis and dual basis has the concrete
alternating coordinate matrix. -/
theorem toMatrix_tensorPolarMap_basis (D : AddSubgroup B) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (A : TensorCoordinates d) :
    LinearMap.toMatrix e e.dualBasis (tensorPolarLinearMap D (basisParameter D e) A) =
      tensorAlternatingMatrix A := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [e.dualBasis_repr]
  exact tensorPolarMap_basis_entry D e A i j

/-- Matrix rank equals the intrinsic polar rank of the actual quadratic
function on the prescribed domain. -/
theorem tensorPolarRank_basis_eq_matrix_rank (D : AddSubgroup B) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) D) (A : TensorCoordinates d) :
    tensorPolarRank D (basisParameter D e) A = (tensorAlternatingMatrix A).rank := by
  rw [← tensorPolarLinearMap_finrank_range D (basisParameter D e) A]
  rw [← toMatrix_tensorPolarMap_basis D e A]
  symm
  have h := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix e e.dualBasis (tensorPolarLinearMap D (basisParameter D e) A))
    e.dualBasis e
  rw [Matrix.toLin_toMatrix] at h
  exact h

/-- Above the diagonal, the alternating coordinate matrix recovers the tensor
coordinate literally. -/
theorem tensorAlternatingMatrix_apply_lt {d : ℕ} (A : TensorCoordinates d)
    {i j : Fin d} (hij : i < j) : tensorAlternatingMatrix A i j = A ⟨(i, j), hij⟩ := by
  classical
  unfold tensorAlternatingMatrix
  let key : TensorIndex d := ⟨(i, j), hij⟩
  have hs : (Finset.univ.sum fun kl : TensorIndex d ↦ A kl *
      ((if kl.val.1 = j then 1 else 0) * (if kl.val.2 = i then 1 else 0) +
        (if kl.val.2 = j then 1 else 0) * (if kl.val.1 = i then 1 else 0))) =
      A key *
        ((if key.val.1 = j then 1 else 0) * (if key.val.2 = i then 1 else 0) +
          (if key.val.2 = j then 1 else 0) * (if key.val.1 = i then 1 else 0)) := by
    apply Finset.sum_eq_single key
    · intro kl hkl hne
      rcases kl with ⟨⟨k, l⟩, hlt⟩
      simp only [Finset.mem_univ, ne_eq] at hne
      have hforward :
          (if k = j then (1 : ZMod 2) else 0) * (if l = i then 1 else 0) = 0 := by
        by_cases hkj : k = j
        · by_cases hli : l = i
          · subst k
            subst l
            exfalso
            exact (not_lt_of_ge (le_of_lt hij)) hlt
          · simp [hli]
        · simp [hkj]
      have hreverse :
          (if l = j then (1 : ZMod 2) else 0) * (if k = i then 1 else 0) = 0 := by
        by_cases hlj : l = j
        · by_cases hki : k = i
          · exfalso
            apply hne
            apply Subtype.ext
            simp [key, hki, hlj]
          · simp [hki]
        · simp [hlj]
      rw [hforward, hreverse]
      simp
    · simp
  calc
    (∑ kl : TensorIndex d, A kl *
      ((if kl.val.1 = j then 1 else 0) * (if kl.val.2 = i then 1 else 0) +
        (if kl.val.2 = j then 1 else 0) * (if kl.val.1 = i then 1 else 0))) =
        A ⟨(i, j), hij⟩ *
          ((if i = j then 1 else 0) * (if j = i then 1 else 0) + 1 * 1) := by
      simpa [key] using hs
    _ = A ⟨(i, j), hij⟩ := by simp [ne_of_lt hij, ne_of_gt hij]

/-- The coordinate assignment from tensors to alternating matrices is
injective. -/
theorem tensorAlternatingMatrix_injective {d : ℕ} :
    Function.Injective (tensorAlternatingMatrix : TensorCoordinates d →
      Matrix (Fin d) (Fin d) (ZMod 2)) := by
  intro A C h
  funext ij
  exact (tensorAlternatingMatrix_apply_lt A ij.property).symm.trans
    ((congrFun (congrFun h ij.val.1) ij.val.2).trans
      (tensorAlternatingMatrix_apply_lt C ij.property))

end BinaryFieldCounterexamples.Gold
