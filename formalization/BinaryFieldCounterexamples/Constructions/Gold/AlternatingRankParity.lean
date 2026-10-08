/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicSplit
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingCoordinates
/-!
# Even rank for actual binary alternating forms and tensors

Dimension induction splits off a hyperbolic plane from each nonzero form.
This handles arbitrary alternating forms directly, without first supplying a
quadratic refinement, and specializes to the literal tensor coordinate matrix.
-/
@[expose] public section
universe u
namespace BinaryFieldCounterexamples.Gold
/-- Every finite binary symmetric alternating form has even rank. -/
theorem symmetric_alternating_rank_even
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) :
    Even (Module.finrank (ZMod 2) (LinearMap.range C)) := by
  have aux : ∀ n : ℕ, ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W],
      Module.finrank (ZMod 2) W=n →
      ∀ (B : W →ₗ[ZMod 2] Module.Dual (ZMod 2) W),
        (∀ a b, B a b=B b a) → (∀ a, B a a=0) →
        Even (Module.finrank (ZMod 2) (LinearMap.range B)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hn B hs ha
      by_cases hB : B=0
      · subst B
        rw [LinearMap.range_zero, finrank_bot]
        exact ⟨0, rfl⟩
      · obtain ⟨x,y,hxy⟩ := exists_hyperbolic_pair B hB
        have hd := hyperbolicComplement_finrank B x y hs ha hxy
        have hr := hyperbolicRestrictedMap_rank B x y hs ha hxy
        have he := ih (Module.finrank (ZMod 2) (hyperbolicComplement B x y))
          (by omega) (hyperbolicComplement B x y) rfl
          (hyperbolicRestrictedMap B x y)
          (hyperbolicRestrictedMap_symmetric B x y hs)
          (hyperbolicRestrictedMap_alternating B x y ha)
        rw [hr]
        exact he.add (by decide : Even 2)
  exact aux _ V rfl C hs ha
/-- The actual upper-coordinate tensor matrix has even rank. -/
theorem tensorAlternatingMatrix_rank_even (d : ℕ) (A : TensorIndex d → ZMod 2) :
    Even (tensorAlternatingMatrix A).rank := by
  rw [matrix_rank_eq_matrixPolarMap_finrank]
  apply symmetric_alternating_rank_even
  · intro x y
    rw [matrixPolarMap_apply,matrixPolarMap_apply]
    have h := Matrix.dotProduct_transpose_mulVec (tensorAlternatingMatrix A) y x
    rwa [tensorAlternatingMatrix_transpose] at h
  · intro x
    rw [matrixPolarMap_apply]
    exact tensorAlternatingMatrix_alternating A x
end BinaryFieldCounterexamples.Gold
