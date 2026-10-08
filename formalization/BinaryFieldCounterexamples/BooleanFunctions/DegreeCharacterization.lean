/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeAffine

/-!
# Boolean functions of degree at most one

The degree-one criterion in the height-two proof of Lemma 6.4 identifies affine
Boolean functions intrinsically: their reduced polynomial has only constant
and single-variable terms. This module proves both directions of that criterion.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial BigOperators
open scoped Classical
variable {σ : Type*} [Fintype σ]

/-- Every polynomial of total degree at most one is its constant plus its linear terms. -/
theorem polynomial_eq_affine_of_totalDegree_le_one (p : MvPolynomial σ (ZMod 2))
    (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + ∑ i, C (p.coeff (Finsupp.single i 1)) * X i := by
  ext d
  by_cases hd0 : d = 0
  · subst d
    simp [coeff_C_mul, coeff_X]
  by_cases hd1 : ∃ i, d = Finsupp.single i 1
  · obtain ⟨j, rfl⟩ := hd1
    simp [coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, eq_comm]
  have hs : 1 < d.sum (fun _ n => n) := by
    have hzero : d.sum (fun _ n => n) ≠ 0 := by
      intro h
      apply hd0
      ext i
      change d i = 0
      have hi : d i ≤ d.sum (fun _ n => n) := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hone : d.sum (fun _ n => n) ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := Finsupp.sum_eq_one_iff d |>.mp h
      exact hd1 ⟨i, hi⟩
    omega
  have hcoeff : p.coeff d = 0 :=
    coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hp hs)
  have hsingle : ∀ i, d ≠ Finsupp.single i 1 := fun i h => hd1 ⟨i, h⟩
  simp [coeff_C_mul, coeff_X, hd0, hsingle, hcoeff, eq_comm]

/-- A Boolean function has degree at most one exactly when it is an affine
combination of its linear coordinates. -/
theorem degree_le_one_iff_affine_combination (f : (σ → ZMod 2) → ZMod 2) :
    degree f ≤ 1 ↔ ∃ (a : σ → ZMod 2) (c : ZMod 2),
      f = fun x => c + ∑ i, a i * x i := by
  constructor
  · intro h
    refine ⟨fun i => (anf f).coeff (Finsupp.single i 1), (anf f).coeff 0, ?_⟩
    funext x
    have hp := polynomial_eq_affine_of_totalDegree_le_one (anf f) h
    simpa using congrArg (eval x) hp
  · rintro ⟨a, c, rfl⟩
    exact degree_affine_combination_le a c

/-- Degree at most one is equivalent to representation by an affine scalar map. -/
theorem degree_le_one_iff_exists_affineMap (f : (σ → ZMod 2) → ZMod 2) :
    degree f ≤ 1 ↔ ∃ A : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2, (A : _ → _) = f := by
  constructor
  · intro h
    obtain ⟨a, c, hf⟩ := (degree_le_one_iff_affine_combination f).mp h
    let L : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i, a i • LinearMap.proj i
    refine ⟨L.toAffineMap + AffineMap.const (ZMod 2) _ c, ?_⟩
    funext x
    simp [L, hf, add_comm]
  · rintro ⟨A, rfl⟩
    exact degree_affine_le A

/-- The intrinsic degree-one criterion holds on every finite-dimensional binary space. -/
theorem vectorDegree_le_one_iff_exists_affineMap {U : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U] (f : U → ZMod 2) :
    vectorDegree f ≤ 1 ↔ ∃ A : U →ᵃ[ZMod 2] ZMod 2, (A : _ → _) = f := by
  constructor
  · intro h
    let b := (Module.finBasis (ZMod 2) U).equivFun
    obtain ⟨A, hA⟩ := (degree_le_one_iff_exists_affineMap (f ∘ b.symm)).mp h
    refine ⟨A.comp b.toAffineEquiv.toAffineMap, ?_⟩
    funext x
    simpa [Function.comp_def] using congrFun hA (b x)
  · rintro ⟨A, rfl⟩
    exact vectorDegree_affine_le A

end BinaryFieldCounterexamples.BooleanFunctions
