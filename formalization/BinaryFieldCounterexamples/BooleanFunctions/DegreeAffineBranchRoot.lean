/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBranch
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBranchCoordinates
/-!
# Affine coordinates in the top-degree root argument

Lemma 6.5 (Section 6.2, p. 61) allows translated child coordinates. The selector
is still a linear functional, so the translation has zero selector component.
Absorbing its other components into the children reduces the affine case to
the linear coordinate argument without changing either child's degree.
-/
@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions
variable {V W U : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

omit [Finite V] [Finite W] [Finite U] in
/-- A linear selector forces the translation in affine branch coordinates to
lie entirely in the child blocks. -/
theorem affineBranch_selector_zero
    (a : U →ᵃ[ZMod 2] (ZMod 2 × V × W))
    (s : Module.Dual (ZMod 2) U) (hsel : ∀ x, (a x).1=s x) : (a 0).1=0 := by
  simpa using hsel 0

omit [Finite V] [Finite W] [Finite U] in
/-- Remove the constant child offsets from affine branch coordinates. -/
theorem branch_affine_eq_linear_translated
    (f : V → ZMod 2) (g : W → ZMod 2)
    (a : U →ᵃ[ZMod 2] (ZMod 2 × V × W)) (hzero : (a 0).1=0) :
    (fun x => Trees.branch f g (a x)) =
      fun x => Trees.branch (fun v => f ((a 0).2.1+v))
        (fun w => g ((a 0).2.2+w)) (a.linear x) := by
  funext x
  have ha : a x=a.linear x+a 0 := congrFun a.decomp x
  rw [ha]
  simp [Trees.branch, hzero, add_comm]

omit [Finite V] [Finite W] [Finite U] in
/-- The linear part retains the same selector functional. -/
theorem affineBranch_linear_selector
    (a : U →ᵃ[ZMod 2] (ZMod 2 × V × W))
    (s : Module.Dual (ZMod 2) U) (hsel : ∀ x, (a x).1=s x) :
    ∀ x, (a.linear x).1=s x := by
  intro x
  have hzero := affineBranch_selector_zero a s hsel
  have ha : a x=a.linear x+a 0 := congrFun a.decomp x
  simpa [ha, hzero] using hsel x

/-- Lemma 6.5's top-degree characterization in surjective affine coordinates.
Both children have the same degree at least two. Only the nonzero selector
functional can multiply their independent branch without increasing its degree.
The coordinate proof retains all unused ambient directions as a separate block. -/
theorem root_degree_characterization_affinePullback
    (f : V → ZMod 2) (g : W → ZMod 2)
    (a : U →ᵃ[ZMod 2] (ZMod 2 × V × W)) (ha : Function.Surjective a)
    (s : Module.Dual (ZMod 2) U) (hsel : ∀ x, (a x).1=s x)
    (ℓ : Module.Dual (ZMod 2) U) (hℓ : ℓ≠0)
    {k : ℕ} (hk : 2≤k) (hf : vectorDegree f=k) (hg : vectorDegree g=k) :
    vectorDegree (fun x => ℓ x*Trees.branch f g (a x))≤k+1 ↔ ℓ=s := by
  let f' := fun v => f ((a 0).2.1+v)
  let g' := fun w => g ((a 0).2.2+w)
  have hf' : vectorDegree f'=k :=
    (vectorDegree_comp_affineEquiv f
      (AffineEquiv.constVAdd (ZMod 2) V (a 0).2.1)).trans hf
  have hg' : vectorDegree g'=k :=
    (vectorDegree_comp_affineEquiv g
      (AffineEquiv.constVAdd (ZMod 2) W (a 0).2.2)).trans hg
  have hbranch := branch_affine_eq_linear_translated f g a
    (affineBranch_selector_zero a s hsel)
  have hprod : (fun x => ℓ x*Trees.branch f g (a x))=
      fun x => ℓ x*Trees.branch f' g' (a.linear x) := by
    funext x
    rw [congrFun hbranch x]
  rw [hprod]
  exact root_degree_characterization_linearPullback f' g' a.linear
    (a.linear_surjective_iff.mpr ha) s (affineBranch_linear_selector a s hsel)
    ℓ hℓ hk hf' hg'

end BinaryFieldCounterexamples.BooleanFunctions
