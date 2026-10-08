/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Affine functions giving the challenges, from recursive locator cancellation

This file defines the scalar recursion used to cancel the leading terms of
binary subspace locators and packages its residual coefficient as an affine
function of the free cancellation parameters.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

namespace AllRatesConstruction

open Finset

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Evaluation commutes with a finite sum of affine maps. -/
theorem affineMap_sum_apply {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {ι : Type*} (S : Finset ι) (f : ι → (V →ᵃ[F] F)) (x : V) :
    (∑ i ∈ S, f i) x = ∑ i ∈ S, f i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih]

/-- The affine recursion which cancels successive locator coefficients. -/
def cancellationCoeffAffine {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) : ℕ → ((ℕ → F) →ᵃ[F] F)
  | 0 => AffineMap.const F (ℕ → F) 1
  | j + 1 => (LinearMap.proj (R := F) (φ := fun _ : ℕ => F) (j + 1)).toAffineMap +
      ∑ ii : {i // i ∈ Finset.range (j + 1)},
        (a (j + 1 - ii.1) ^ (2 ^ (s - 1 - ii.1))) •
          cancellationCoeffAffine s a ii.1
  termination_by j => j
  decreasing_by
  have hii := Finset.mem_range.mp ii.2
  omega

/-- Recursive cancellation coefficients, with `b₀=1`. -/
def cancellationCoeff {F : Type*} [Field F]
    (s : ℕ) (a θ : ℕ → F) (j : ℕ) : F :=
  cancellationCoeffAffine s a j θ

@[simp]
theorem cancellationCoeff_zero {F : Type*} [Field F]
    (s : ℕ) (a θ : ℕ → F) : cancellationCoeff s a θ 0 = 1 := by
  rw [cancellationCoeff, cancellationCoeffAffine.eq_1]
  exact AffineMap.const_apply F (ℕ → F) 1 θ

@[simp]
theorem cancellationCoeff_succ {F : Type*} [Field F]
    (s : ℕ) (a θ : ℕ → F) (j : ℕ) :
    cancellationCoeff s a θ (j + 1) = θ (j + 1) +
      ∑ i ∈ Finset.range (j + 1), cancellationCoeff s a θ i *
        a (j + 1 - i) ^ (2 ^ (s - 1 - i)) := by
  rw [cancellationCoeff, cancellationCoeffAffine.eq_2]
  simp only [AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
    LinearMap.proj_apply]
  simp only [affineMap_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_subtype (s := Finset.range (j + 1))
    (fun i ↦ Iff.rfl)
    (fun i ↦ a (j + 1 - i) ^ (2 ^ (s - 1 - i)) *
      cancellationCoeffAffine s a i θ)]
  simp only [cancellationCoeff]
  apply congrArg (fun z ↦ θ (j + 1) + z)
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The residual challenge after the first `s-1` cancellations. -/
def cancellationLabelAffine {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) : (ℕ → F) →ᵃ[F] F :=
  ∑ i ∈ Finset.range s,
    (a (s - i) ^ (2 ^ (s - 1 - i))) • cancellationCoeffAffine s a i

/-- Evaluation of the residual cancellation challenge. -/
def cancellationLabel {F : Type*} [Field F]
    (s : ℕ) (a θ : ℕ → F) : F :=
  cancellationLabelAffine s a θ

@[simp]
theorem cancellationLabel_apply {F : Type*} [Field F]
    (s : ℕ) (a θ : ℕ → F) :
    cancellationLabel s a θ =
      ∑ i ∈ Finset.range s, cancellationCoeff s a θ i *
        a (s - i) ^ (2 ^ (s - 1 - i)) := by
  rw [cancellationLabel, cancellationLabelAffine,
    affineMap_sum_apply]
  simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, cancellationCoeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- Embed the `s-1` genuine cancellation parameters into the one-based
parameter sequence used by `cancellationCoeff`. -/
def finiteCancellationParameterExtension {F : Type*} [Field F]
    (s : ℕ) : (Fin (s - 1) → F) →ₗ[F] (ℕ → F) := by
  exact
    { toFun := fun θ j ↦ if h : 1 ≤ j ∧ j < s then θ ⟨j - 1, by omega⟩ else 0
      map_add' := by
        intro θ ψ
        ext j
        by_cases h : 1 ≤ j ∧ j < s
        · simp [h]
        · simp [h]
      map_smul' := by
        intro c θ
        ext j
        by_cases h : 1 ≤ j ∧ j < s
        · simp [h]
        · simp [h] }


@[simp]
theorem finiteCancellationParameterExtension_apply_of_mem
    {F : Type*} [Field F] (s : ℕ) (θ : Fin (s - 1) → F)
    (j : ℕ) (hj1 : 1 ≤ j) (hjs : j < s) :
    finiteCancellationParameterExtension s θ j = θ ⟨j - 1, by omega⟩ := by
  simp [finiteCancellationParameterExtension, hj1, hjs]

@[simp]
theorem finiteCancellationParameterExtension_apply_zero
    {F : Type*} [Field F] (s : ℕ) (θ : Fin (s - 1) → F) :
    finiteCancellationParameterExtension s θ 0 = 0 := by
  simp [finiteCancellationParameterExtension]

/-- The residual challenge as an affine function of its `s-1` genuine parameters. -/
def finiteCancellationLabelAffine {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) : (Fin (s - 1) → F) →ᵃ[F] F :=
  (cancellationLabelAffine s a).comp
    (finiteCancellationParameterExtension s).toAffineMap

@[simp]
theorem finiteCancellationLabelAffine_apply
    {F : Type*} [Field F] (s : ℕ) (a : ℕ → F)
    (θ : Fin (s - 1) → F) :
    finiteCancellationLabelAffine s a θ =
      cancellationLabel s a (finiteCancellationParameterExtension s θ) := by
  rfl

end AllRatesConstruction

end BinaryFieldCounterexamples
