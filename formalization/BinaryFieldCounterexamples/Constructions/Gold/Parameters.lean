/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.FunctionalInterpolants
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# The binary Gold parameter space

The square root of the linear coefficient identifies each binary functional
on the prescribed domain with a field element. Its image is the parameter
subgroup `W` in the Gold locator lemma. The map is injective because the
canonical Artin--Schreier equation determines a zero-constant representative
from that coefficient.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

open Polynomial

variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- The linear coefficient of the canonical polynomial, as an additive map. -/
noncomputable def functionalLinearCoefficient (D : AddSubgroup B) : (D →+ ZMod 2) →+ B :=
  { toFun := fun l ↦ (functionalPolynomial D l).coeff 1
    map_zero' := by simp [functionalPolynomial_zero]
    map_add' := fun l k ↦ by rw [functionalPolynomial_add, coeff_add] }

/-- The linear coefficient already determines the functional. -/
theorem functionalLinearCoefficient_injective (D : AddSubgroup B) :
    Function.Injective (functionalLinearCoefficient D) := by
  apply (injective_iff_map_eq_zero (functionalLinearCoefficient D)).mpr
  intro l hl
  apply functionalPolynomial_injective D
  rw [functionalPolynomial_zero]
  exact functionalPolynomial_eq_zero_of_coeff_one_eq_zero D l hl

/-- Gold's parameter `c` is the unique square root of the canonical
representative's linear coefficient. -/
noncomputable def functionalParameter (D : AddSubgroup B) : (D →+ ZMod 2) →+ B :=
  (frobeniusEquiv B 2).symm.toAddMonoidHom.comp (functionalLinearCoefficient D)

/-- Squaring the parameter recovers the representative's linear coefficient. -/
theorem functionalParameter_sq (D : AddSubgroup B) (l : D →+ ZMod 2) :
    functionalParameter D l ^ 2 = (functionalPolynomial D l).coeff 1 := by
  exact frobeniusEquiv_symm_pow_p B 2 _

/-- Different functionals give different Gold parameters. -/
theorem functionalParameter_injective (D : AddSubgroup B) :
    Function.Injective (functionalParameter D) := by
  exact (frobeniusEquiv B 2).symm.injective.comp (functionalLinearCoefficient_injective D)

/-- The concrete binary additive subgroup of Gold parameters. -/
noncomputable def parameterDomain (D : AddSubgroup B) : AddSubgroup B :=
  (functionalParameter D).range

/-- The parameter map identifies the binary dual with its concrete image. -/
noncomputable def parameterEquiv (D : AddSubgroup B) :
    (D →+ ZMod 2) ≃+ parameterDomain D :=
  { Equiv.ofInjective (functionalParameter D) (functionalParameter_injective D) with
    map_add' := fun l k ↦ Subtype.ext (map_add (functionalParameter D) l k) }

/-- The Gold parameter space has exactly the same size as the original domain. -/
theorem card_parameterDomain (D : AddSubgroup B) :
    Nat.card (parameterDomain D) = Nat.card D := by
  classical
  rw [← Nat.card_congr (parameterEquiv D).toEquiv]
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2 (M := D) (M₁ := ZMod 2)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
    ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]

/-- The canonical polynomial attached to a field parameter in `W`. -/
noncomputable def parameterPolynomial (D : AddSubgroup B) (c : parameterDomain D) : B[X] :=
  functionalPolynomial D ((parameterEquiv D).symm c)

/-- Reparametrizing by `W` preserves the canonical representative. -/
theorem parameterPolynomial_apply (D : AddSubgroup B) (l : D →+ ZMod 2) :
    parameterPolynomial D (parameterEquiv D l) = functionalPolynomial D l := by
  simp [parameterPolynomial]

/-- The square of a field parameter is its polynomial's linear coefficient. -/
theorem parameterPolynomial_coeff_one (D : AddSubgroup B) (c : parameterDomain D) :
    (parameterPolynomial D c).coeff 1 = (c : B) ^ 2 := by
  rw [parameterPolynomial, ← functionalParameter_sq]
  have h := congrArg (fun z : parameterDomain D ↦ (z : B))
    ((parameterEquiv D).apply_symm_apply c)
  exact congrArg (· ^ 2) h

/-- The parameterized Artin--Schreier identity with the paper's `c²` coefficient. -/
theorem functionalParameter_artinSchreier
    (D : AddSubgroup B) [Fintype D] (l : D →+ ZMod 2) :
    (functionalPolynomial D l) ^ 2 + functionalPolynomial D l =
      C (functionalParameter D l ^ 2) *
        (C (((subspacePolynomial D).coeff 1)⁻¹) * subspacePolynomial D) := by
  rw [functionalParameter_sq]
  exact functionalPolynomial_artinSchreier D l

/-- The domain locator normalized to have derivative one. -/
noncomputable def normalizedLocator (D : AddSubgroup B) [Fintype D] : B[X] :=
  C (((subspacePolynomial D).coeff 1)⁻¹) * subspacePolynomial D

/-- The normalized locator has formal derivative one. -/
theorem normalizedLocator_derivative {B : Type*} [Field B] [CharP B 2]
    (D : AddSubgroup B) [Fintype D] :
    (normalizedLocator D).derivative = 1 := by
  rw [normalizedLocator, derivative_C_mul,
    derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D), ← C_mul,
    inv_mul_cancel₀ (subspacePolynomial_coeff_one_ne_zero D), C_1]

/-- Gold's scaling factor is the canonical square root of the inverse linear
coefficient of the locator. -/
noncomputable def normalizingRoot (D : AddSubgroup B) [Fintype D] : B :=
  (frobeniusEquiv B 2).symm (((subspacePolynomial D).coeff 1)⁻¹)

/-- The scaling factor satisfies the exact square relation used in leading
coefficient recovery. -/
theorem normalizingRoot_sq {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) [Fintype D] :
    normalizingRoot D ^ 2 = ((subspacePolynomial D).coeff 1)⁻¹ := by
  exact frobeniusEquiv_symm_pow_p B 2 _

/-- The normalization factor cannot vanish. -/
theorem normalizingRoot_ne_zero {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) [Fintype D] :
    normalizingRoot D ≠ 0 := by
  intro h
  have he := normalizingRoot_sq D
  rw [h, zero_pow (by decide)] at he
  exact (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D)) he.symm

/-- Zero has the zero parameter polynomial. -/
theorem parameterPolynomial_zero (D : AddSubgroup B) : parameterPolynomial D 0 = 0 := by
  simp [parameterPolynomial, functionalPolynomial_zero]

/-- Parameter polynomials vary additively with the field parameter. -/
theorem parameterPolynomial_add (D : AddSubgroup B) (c e : parameterDomain D) :
    parameterPolynomial D (c + e) = parameterPolynomial D c + parameterPolynomial D e := by
  simp [parameterPolynomial, functionalPolynomial_add]

/-- Reparametrization preserves binary support and the half-domain degree bound. -/
theorem parameterPolynomial_support_and_degree (D : AddSubgroup B) (c : parameterDomain D) :
    BinaryLocator.IsBinaryLinearized (parameterPolynomial D c) ∧
      (parameterPolynomial D c).natDegree ≤ Nat.card D / 2 := by
  exact functionalPolynomial_support_and_degree D _

/-- The parameter polynomial's formal derivative is the constant `c²`. -/
theorem parameterPolynomial_derivative (D : AddSubgroup B) (c : parameterDomain D) :
    (parameterPolynomial D c).derivative = C ((c : B) ^ 2) := by
  rw [derivative_eq_C_of_binarySupport _ (parameterPolynomial_support_and_degree D c).1,
    parameterPolynomial_coeff_one]

/-- The canonical polynomial with parameter `c` has Artin--Schreier image
`c²` times the normalized locator. -/
theorem parameterPolynomial_artinSchreier
    (D : AddSubgroup B) [Fintype D] (c : parameterDomain D) :
    parameterPolynomial D c ^ 2 + parameterPolynomial D c = C ((c : B) ^ 2) * normalizedLocator D := by
  rw [← parameterPolynomial_coeff_one]
  exact functionalPolynomial_artinSchreier D _

end BinaryFieldCounterexamples.Gold
