/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Transporting locators through a field embedding

An injective field map transports both the roots and the entire product
locator. Thus the same quadratic coefficient pair computed over the source
field gives exactly the challenge coefficients of the embedded subgroup.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- A field embedding preserves the size of an additive subgroup. -/
theorem natCard_map_addSubgroup
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (W : AddSubgroup B) :
    Nat.card (W.map φ.toAddMonoidHom) = Nat.card W := by
  exact AddSubgroup.card_map_of_injective φ.injective

/-- Mapping the coefficients of a locator is exactly the product locator of
the embedded subgroup. The equivalence reindexes the original roots. -/
theorem map_subspacePolynomial
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (W : AddSubgroup B) [Fintype W] [Fintype (W.map φ.toAddMonoidHom)] :
    (subspacePolynomial W).map φ = subspacePolynomial (W.map φ.toAddMonoidHom) := by
  classical
  unfold subspacePolynomial
  rw [Polynomial.map_prod]
  apply Fintype.prod_equiv (W.equivMapOfInjective φ.toAddMonoidHom φ.injective).toEquiv
  intro w
  simp only [Polynomial.map_sub, map_X, map_C]
  congr 2

/-- Each coefficient of the embedded locator is the image of the original
coefficient, including the two coefficients used in quadratic challenges. -/
theorem coeff_subspacePolynomial_map
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (W : AddSubgroup B) [Fintype W] [Fintype (W.map φ.toAddMonoidHom)] (n : ℕ) :
    (subspacePolynomial (W.map φ.toAddMonoidHom)).coeff n =
      φ ((subspacePolynomial W).coeff n) := by
  rw [← map_subspacePolynomial φ W, coeff_map]

end BinaryFieldCounterexamples
