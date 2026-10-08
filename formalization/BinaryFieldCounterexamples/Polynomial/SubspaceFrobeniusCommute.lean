/- Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license. -/
module
public import BinaryFieldCounterexamples.Polynomial.BinarySupport
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
set_option autoImplicit false

/-- Coefficient Frobenius fixes a finite field, so the full-cardinality power
of an actual polynomial equals substitution of the full-cardinality power of X. -/
theorem polynomial_pow_card_eq_comp
    {B : Type*} [Field B] [Fintype B] (P : B[X]) :
    P ^ Fintype.card B = P.comp (X ^ Fintype.card B) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [show (P+Q)^Fintype.card B=P^Fintype.card B+Q^Fintype.card B from
        (FiniteField.frobeniusAlgHom B B[X]).map_add P Q, hP, hQ, add_comp]
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      simp only [mul_pow, ← C.map_pow, FiniteField.pow_card, mul_comp, C_comp, pow_comp, X_comp]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm n]

/-- Prime-power support gives a literal additive composition identity. -/
theorem subspacePolynomial_comp_add
    {B : Type*} [Field B] [CharP B 2] (D : AddSubgroup B) [Fintype D]
    (P Q : B[X]) :
    (subspacePolynomial D).comp (P+Q) =
      (subspacePolynomial D).comp P + (subspacePolynomial D).comp Q := by
  classical
  simp only [comp_eq_sum_left, Polynomial.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨i,rfl⟩ := subspacePolynomial_support D j hj
  rw [add_pow_char_pow P Q 2 i, mul_add]

/-- The actual locator commutes with the finite-field vanishing polynomial. -/
theorem subspacePolynomial_comp_frobenius_sub
    {B : Type*} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) [Fintype D] :
    (subspacePolynomial D).comp (X ^ Fintype.card B-X) =
      ((X : B[X]) ^ Fintype.card B-X).comp (subspacePolynomial D) := by
  rw [CharTwo.sub_eq_add, subspacePolynomial_comp_add, comp_X,
    ← polynomial_pow_card_eq_comp, add_comp, X_pow_comp, X_comp]

/-- Characteristic-two form of the same actual composition identity. -/
theorem subspacePolynomial_comp_frobenius_add
    {B : Type*} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) [Fintype D] :
    (subspacePolynomial D).comp (X ^ Fintype.card B+X) =
      ((X : B[X]) ^ Fintype.card B+X).comp (subspacePolynomial D) := by
  simpa only [CharTwo.sub_eq_add] using subspacePolynomial_comp_frobenius_sub D
end BinaryFieldCounterexamples
