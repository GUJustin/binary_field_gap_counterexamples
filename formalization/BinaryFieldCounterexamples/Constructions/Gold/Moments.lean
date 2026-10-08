/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.TensorPolynomials
/-!
# Gold moment equations in concrete tensor coordinates

The canonical Artin--Schreier equation gives a triangular coefficient
recurrence depending on the prescribed domain's normalized locator. Expanding
that recurrence identifies the additive derivative's low coefficients with
squared Gold moments. Initial moment vanishing therefore removes precisely
the required low binary exponents, without assumptions on the shape of the
domain locator.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- A Gold moment of a concrete alternating tensor over the parameter space. -/
noncomputable def goldMoment (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (r : ℕ) : B :=
  ∑ ij : TensorIndex d, algebraMap (ZMod 2) B (A ij) *
    ((v ij.val.1 : B) * (v ij.val.2 : B)^(2^r) +
      (v ij.val.2 : B) * (v ij.val.1 : B)^(2^r))
/-- The zeroth moment vanishes by alternation in characteristic two. -/
theorem goldMoment_zero (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    goldMoment D v A 0 = 0 := by
  unfold goldMoment
  apply Finset.sum_eq_zero
  intro ij _
  simp only [pow_zero, pow_one]
  rw [mul_comm (v ij.val.2 : B), CharTwo.add_self_eq_zero, mul_zero]
/-- The normalized locator has unit linear coefficient. -/
theorem normalizedLocator_coeff_one {B : Type*} [Field B] (D : AddSubgroup B) [Fintype D] :
    (normalizedLocator D).coeff 1 = 1 := by
  rw [normalizedLocator, coeff_C_mul, inv_mul_cancel₀ (subspacePolynomial_coeff_one_ne_zero D)]
/-- Coefficients of the canonical functional satisfy the exact upward recurrence. -/
theorem parameterPolynomial_coeff_recurrence (D : AddSubgroup B) [Fintype D]
    (c : parameterDomain D) (i : ℕ) :
    (parameterPolynomial D c).coeff (2^(i+1)) =
      (parameterPolynomial D c).coeff (2^i)^2 +
      (c : B)^2 * (normalizedLocator D).coeff (2^(i+1)) := by
  have he := congrArg (fun P : B[X] ↦ P.coeff (2^(i+1)))
    (parameterPolynomial_artinSchreier D c)
  rw [coeff_add, coeff_C_mul, pow_succ 2 i, mul_comm (2^i) 2, coeff_sq_double] at he
  rw [pow_succ 2 i, mul_comm (2^i) 2, ← he]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
/-- Explicit coefficients of each functional in terms of the prescribed locator. -/
theorem parameterPolynomial_coeff_expansion (D : AddSubgroup B) [Fintype D]
    (c : parameterDomain D) (i : ℕ) :
    (parameterPolynomial D c).coeff (2^i) =
      ∑ r ∈ Finset.range (i+1),
        (normalizedLocator D).coeff (2^(i-r)) ^ (2^r) * (c : B)^(2^(r+1)) := by
  induction i with
  | zero => simp [parameterPolynomial_coeff_one, normalizedLocator_coeff_one]
  | succ i ih =>
    rw [parameterPolynomial_coeff_recurrence, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_one, Nat.sub_zero]
    rw [sum_pow_char]
    simp only [mul_pow, ← pow_mul, ← pow_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro r hr
      simp only [Nat.add_sub_add_right]
    · ring
/-- The zero-constant additive part of a tensor polynomial's derivative. -/
noncomputable def tensorLinearPart (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : B[X] :=
  ∑ ij : TensorIndex d, C (algebraMap (ZMod 2) B (A ij)) *
    (C ((v ij.val.1 : B)^2) * parameterPolynomial D (v ij.val.2) +
      C ((v ij.val.2 : B)^2) * parameterPolynomial D (v ij.val.1))

/-- Binary field scalars are fixed by squaring. -/
theorem binaryScalar_sq {B : Type*} [Field B] [Algebra (ZMod 2) B] (a : ZMod 2) :
    algebraMap (ZMod 2) B a ^ 2 = algebraMap (ZMod 2) B a := by
  rcases binary_eq_zero_or_one a with rfl | rfl <;> simp

/-- The coefficients of the additive derivative are triangular combinations of squared Gold moments. -/
theorem tensorLinearPart_coeff_expansion (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (i : ℕ) :
    (tensorLinearPart D v A).coeff (2^i) =
      ∑ r ∈ Finset.range (i+1),
        (normalizedLocator D).coeff (2^(i-r)) ^ (2^r) * goldMoment D v A r ^ 2 := by
  classical
  simp only [tensorLinearPart, finsetSum_coeff, coeff_C_mul, coeff_add,
    parameterPolynomial_coeff_expansion]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [goldMoment, sum_pow_char]
  simp only [mul_pow, binaryScalar_sq, CharTwo.add_sq, ← pow_mul, ← pow_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Vanishing initial moments removes all lower binary coefficients of the derivative. -/
theorem tensorLinearPart_coeff_eq_zero (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (i : ℕ) (hi : i < t) : (tensorLinearPart D v A).coeff (2^i) = 0 := by
  rw [tensorLinearPart_coeff_expansion]
  apply Finset.sum_eq_zero
  intro r hr
  have hzero : goldMoment D v A r = 0 := by
    by_cases h : r = 0
    · subst r; exact goldMoment_zero D v A
    · exact hM r (by omega) (by have := Finset.mem_range.mp hr; omega)
  rw [hzero, zero_pow (by decide), mul_zero]

/-- The derivative splits into its additive part and a scalar constant. -/
theorem tensorPolynomial_derivative (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    (tensorPolynomial D v A).derivative = tensorLinearPart D v A +
      C (∑ ij : TensorIndex d, algebraMap (ZMod 2) B (A ij) *
        ((v ij.val.1 : B) * (v ij.val.2 : B))) := by
  classical
  simp only [tensorPolynomial, tensorLinearPart, derivative_C_mul,
    pairPolynomial_derivative, mul_add, map_sum, map_mul, Finset.sum_add_distrib]

/-- Addition preserves binary polynomial support. -/
theorem binarySupport_add {B : Type*} [Field B] [CharP B 2] (P Q : B[X])
    (hP : BinaryLocator.IsBinaryLinearized P) (hQ : BinaryLocator.IsBinaryLinearized Q) :
    BinaryLocator.IsBinaryLinearized (P+Q) := by
  simpa only [CharTwo.sub_eq_add] using BinaryLocator.is_binary_linearized_sub P Q hP hQ

/-- Finite sums preserve binary polynomial support. -/
theorem binarySupport_sum {B : Type*} [Field B] [CharP B 2] {ι : Type*}
    (S : Finset ι) (P : ι → B[X]) (hP : ∀ i ∈ S, BinaryLocator.IsBinaryLinearized (P i)) :
    BinaryLocator.IsBinaryLinearized (∑ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [BinaryLocator.IsBinaryLinearized]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact binarySupport_add _ _ (hP i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)))

/-- The nonconstant derivative has only binary powers in its support. -/
theorem tensorLinearPart_support (D : AddSubgroup B)
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    BinaryLocator.IsBinaryLinearized (tensorLinearPart D v A) := by
  classical
  apply binarySupport_sum
  intro ij _
  apply BinaryLocator.is_binary_linearized_c_mul
  apply binarySupport_add
  · exact BinaryLocator.is_binary_linearized_c_mul _ _
      (parameterPolynomial_support_and_degree D _).1
  · exact BinaryLocator.is_binary_linearized_c_mul _ _
      (parameterPolynomial_support_and_degree D _).1

end BinaryFieldCounterexamples.Gold
