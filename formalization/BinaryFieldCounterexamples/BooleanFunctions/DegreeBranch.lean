/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeRoot
public import BinaryFieldCounterexamples.Constructions.Trees.Templates
public import Mathlib.LinearAlgebra.Pi
/-!
# Degree of independent branches on abstract binary spaces

The recursive degree argument of Lemma 6.4 (Section 6.2, p. 60) uses independent
coordinates for the selector and both children. This module identifies abstract
product spaces with those coordinates and transports `degree_branchFunction`.
The bound is invariant under surjective affine parametrizations, so ignored
ambient coordinates do not change the tree degree.
-/
@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions
variable {V W U : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

/-- Independent coordinates for a selector followed by two abstract child spaces. -/
def branchCoordinateEquiv :
    (Option (Fin (Module.finrank (ZMod 2) V) ⊕ Fin (Module.finrank (ZMod 2) W)) → ZMod 2)
      ≃ₗ[ZMod 2] (ZMod 2 × V × W) :=
  (LinearEquiv.piOptionEquivProd (ZMod 2)).trans
    ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr
      ((LinearEquiv.sumArrowLequivProdArrow _ _ (ZMod 2) (ZMod 2)).trans
        ((Module.finBasis (ZMod 2) V).equivFun.symm.prodCongr
          (Module.finBasis (ZMod 2) W).equivFun.symm)))

/-- The abstract selector reads the `none` coordinate. -/
@[simp] theorem branchCoordinateEquiv_selector (w) :
    (branchCoordinateEquiv (V := V) (W := W) w).1=w none := by rfl

/-- The literal conditional branch is the reduced Boolean selector formula. -/
theorem branch_comp_branchCoordinateEquiv (f : V → ZMod 2) (g : W → ZMod 2) :
    Trees.branch f g ∘ branchCoordinateEquiv =
      branchFunction (f ∘ (Module.finBasis (ZMod 2) V).equivFun.symm)
        (g ∘ (Module.finBasis (ZMod 2) W).equivFun.symm) := by
  funext w
  change (if w none=0 then f ((Module.finBasis (ZMod 2) V).equivFun.symm
    (fun i => w (some (Sum.inl i)))) else
    g ((Module.finBasis (ZMod 2) W).equivFun.symm (fun i => w (some (Sum.inr i))))) = _
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (w none) with hc | hc <;>
    simp [branchFunction, hc, show (1:ZMod 2)+1=0 by decide]

/-- The leading part of an independent branch raises the degree by one.
A positive-degree first child and a second child of no greater degree suffice. -/
theorem vectorDegree_branch (f : V → ZMod 2) (g : W → ZMod 2)
    {k : ℕ} (hk : 0<k) (hf : vectorDegree f=k) (hg : vectorDegree g≤k) :
    vectorDegree (Trees.branch f g)=k+1 := by
  have he := vectorDegree_comp_affineEquiv (Trees.branch f g)
    (branchCoordinateEquiv (V := V) (W := W)).toAffineEquiv
  change vectorDegree (Trees.branch f g ∘ branchCoordinateEquiv)=_ at he
  rw [branch_comp_branchCoordinateEquiv,vectorDegree_eq_degree] at he
  exact he.symm.trans (degree_branchFunction _ _ hk hf hg)

/-- Surjective affine coordinates preserve the degree of the independent branch. -/
theorem vectorDegree_branch_affinePullback (f : V → ZMod 2) (g : W → ZMod 2)
    (a : U →ᵃ[ZMod 2] (ZMod 2 × V × W)) (ha : Function.Surjective a)
    {k : ℕ} (hk : 0<k) (hf : vectorDegree f=k) (hg : vectorDegree g≤k) :
    vectorDegree (fun x => Trees.branch f g (a x))=k+1 := by
  exact (vectorDegree_comp_affine_of_surjective (Trees.branch f g) a ha).trans
    (vectorDegree_branch f g hk hf hg)

end BinaryFieldCounterexamples.BooleanFunctions
