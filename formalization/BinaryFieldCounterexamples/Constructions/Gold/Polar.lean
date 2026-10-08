/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Moments
/-!
# Tensor polarization and the additive derivative

The actual quadratic function on the prescribed domain has a concrete binary
polar functional. Its canonical polynomial has linear coefficient `J(y)`.
Consequently its radical is exactly the set of zeros of `J` on the domain,
and rank-nullity gives the exact radical cardinality. Rank here is the rank
of the actual polar linear map; a coordinate-matrix rank bridge is separate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The literal bilinear polar functional of a tensor at a domain point. -/
noncomputable def tensorPolarFunctional (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) : D →+ ZMod 2 :=
  { toFun := fun x ↦ ∑ ij : TensorIndex d, A ij *
      (((parameterEquiv D).symm (v ij.val.1)) y * ((parameterEquiv D).symm (v ij.val.2)) x +
        ((parameterEquiv D).symm (v ij.val.2)) y * ((parameterEquiv D).symm (v ij.val.1)) x)
    map_zero' := by simp
    map_add' := by
      intro x z
      simp only [map_add, mul_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij _
      ring }
/-- The explicit zero-constant polynomial representing a tensor polar functional. -/
noncomputable def tensorPolarPolynomial (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) : B[X] :=
  ∑ ij : TensorIndex d, C (algebraMap (ZMod 2) B (A ij)) *
    (C ((parameterPolynomial D (v ij.val.1)).eval (y : B)) * parameterPolynomial D (v ij.val.2) +
      C ((parameterPolynomial D (v ij.val.2)).eval (y : B)) * parameterPolynomial D (v ij.val.1))
/-- The explicit polar polynomial evaluates to its actual binary functional. -/
theorem tensorPolarPolynomial_eval (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y x : D) :
    (tensorPolarPolynomial D v A y).eval (x : B) =
      algebraMap (ZMod 2) B ((tensorPolarFunctional D v A y) x) := by
  simp only [tensorPolarPolynomial, tensorPolarFunctional, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, eval_finsetSum, eval_mul, eval_add, eval_C, map_sum, map_mul, map_add,
    parameterPolynomial, functionalPolynomial_eval]
/-- The polar polynomial's linear coefficient is the additive derivative evaluated at the point. -/
theorem tensorPolarPolynomial_coeff_one (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) :
    (tensorPolarPolynomial D v A y).coeff 1 = (tensorLinearPart D v A).eval (y : B) := by
  simp only [tensorPolarPolynomial, tensorLinearPart, finsetSum_coeff, coeff_C_mul,
    coeff_add, parameterPolynomial_coeff_one, eval_finsetSum, eval_mul, eval_add, eval_C]
  apply Finset.sum_congr rfl
  intro ij _
  ring
/-- The polar polynomial has degree at most half the prescribed domain size. -/
theorem tensorPolarPolynomial_natDegree_le (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) :
    (tensorPolarPolynomial D v A y).natDegree ≤ Nat.card D / 2 := by
  classical
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp only [tensorPolarPolynomial, finsetSum_coeff, coeff_C_mul, coeff_add]
  apply Finset.sum_eq_zero
  intro ij _
  rw [coeff_eq_zero_of_natDegree_lt ((parameterPolynomial_support_and_degree D _).2.trans_lt hn),
    coeff_eq_zero_of_natDegree_lt ((parameterPolynomial_support_and_degree D _).2.trans_lt hn)]
  ring
/-- The explicit polar polynomial is the unique canonical functional interpolant. -/
theorem tensorPolarPolynomial_eq_functionalPolynomial (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) :
    tensorPolarPolynomial D v A y = functionalPolynomial D (tensorPolarFunctional D v A y) := by
  apply eq_functionalPolynomial
  · have hn : 0 < Nat.card D := Nat.card_pos
    exact (degree_le_of_natDegree_le (tensorPolarPolynomial_natDegree_le D v A y)).trans_lt
      (by exact_mod_cast Nat.div_lt_self hn (by decide : 1 < 2))
  · exact tensorPolarPolynomial_eval D v A y
/-- The radical of the tensor polar form is exactly the kernel of the additive derivative on D. -/
theorem tensorPolarFunctional_eq_zero_iff (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) :
    tensorPolarFunctional D v A y = 0 ↔ (tensorLinearPart D v A).eval (y : B) = 0 := by
  rw [← tensorPolarPolynomial_coeff_one, tensorPolarPolynomial_eq_functionalPolynomial]
  constructor
  · intro h; rw [h, functionalPolynomial_zero]; simp
  · intro h
    apply functionalPolynomial_injective D
    rw [functionalPolynomial_zero]
    exact functionalPolynomial_eq_zero_of_coeff_one_eq_zero D _ h
/-- The represented functional is the actual polarization of the tensor polynomial on D. -/
theorem tensorPolynomial_polar_eval (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y x : D) :
    (tensorPolynomial D v A).eval ((x+y : D) : B) +
      (tensorPolynomial D v A).eval (x : B) + (tensorPolynomial D v A).eval (y : B) =
      algebraMap (ZMod 2) B ((tensorPolarFunctional D v A y) x) := by
  rw [tensorPolynomial_eval, tensorPolynomial_eval, tensorPolynomial_eval, ← map_add, ← map_add]
  congr 1
  simp only [tensorPolarFunctional, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  linear_combination (norm := ring_nf)
    A ij * (((parameterEquiv D).symm (v ij.val.1)) x * ((parameterEquiv D).symm (v ij.val.2)) x +
      ((parameterEquiv D).symm (v ij.val.1)) y * ((parameterEquiv D).symm (v ij.val.2)) y) *
      (CharTwo.two_eq_zero (R := ZMod 2))
/-- A point is in the radical precisely when it is a zero of the additive derivative. -/
theorem tensorPolynomial_radical_iff (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (y : D) :
    (∀ x : D, (tensorPolynomial D v A).eval ((x+y : D) : B) +
      (tensorPolynomial D v A).eval (x : B) + (tensorPolynomial D v A).eval (y : B) = 0) ↔
      (tensorLinearPart D v A).eval (y : B) = 0 := by
  rw [← tensorPolarFunctional_eq_zero_iff]
  constructor
  · intro h
    ext x
    have he := h x
    rw [tensorPolynomial_polar_eval] at he
    exact (algebraMap (ZMod 2) B).injective (by simpa using he)
  · intro h x
    rw [tensorPolynomial_polar_eval, h]
    simp

/-- The tensor polar form, viewed as a binary linear map into the dual. -/
noncomputable def tensorPolarMap (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : D →ₗ[ZMod 2] (D →+ ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := tensorPolarFunctional D v A
      map_zero' := by ext x; simp [tensorPolarFunctional]
      map_add' := by
        intro y z
        ext x
        simp only [tensorPolarFunctional, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          map_add, AddMonoidHom.add_apply, add_mul, mul_add, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ij _
        ring }
/-- The intrinsic rank of the tensor's actual polar form on the prescribed domain. -/
noncomputable def tensorPolarRank (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (tensorPolarMap D v A))
/-- The radical cardinality is determined exactly by the polar rank. -/
theorem card_tensorPolarMap_ker (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Nat.card (LinearMap.ker (tensorPolarMap D v A)) =
      2 ^ (Module.finrank (ZMod 2) D - tensorPolarRank D v A) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have he := (tensorPolarMap D v A).finrank_range_add_finrank_ker
  have hk : Module.finrank (ZMod 2) (LinearMap.ker (tensorPolarMap D v A)) =
      Module.finrank (ZMod 2) D - tensorPolarRank D v A := by
    unfold tensorPolarRank
    omega
  rw [hk]
  simp

/-- The additive derivative has exactly the radical cardinality of zeros on D. -/
theorem card_tensorLinearPart_zeros (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Nat.card {y : D // (tensorLinearPart D v A).eval (y : B) = 0} =
      Nat.card D / 2 ^ tensorPolarRank D v A := by
  have he : Nat.card {y : D // (tensorLinearPart D v A).eval (y : B) = 0} =
      Nat.card (LinearMap.ker (tensorPolarMap D v A)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro y
    exact (tensorPolarFunctional_eq_zero_iff D v A y).symm
  rw [he, card_tensorPolarMap_ker, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]
  have hr := (tensorPolarMap D v A).finrank_range_add_finrank_ker
  have hr' : tensorPolarRank D v A ≤ Module.finrank (ZMod 2) D := by
    unfold tensorPolarRank
    omega
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  exact (Nat.pow_div hr' (by decide : 0 < 2)).symm

end BinaryFieldCounterexamples.Gold
