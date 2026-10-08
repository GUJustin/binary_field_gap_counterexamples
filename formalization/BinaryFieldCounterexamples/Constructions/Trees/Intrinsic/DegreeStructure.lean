/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.TreeDegree
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeAffineBranchRoot
/-!
# The unique intrinsic root, by top-degree monomials

[Lemma 6.5](../../../../../binary-field-counterexamples.pdf#page=61), in
Section 6.2, characterizes the root by the degree of its product with the tree.
Adapted independent coordinates and the separated monomial types in
`DegreeRoot` force every other block of a candidate linear functional to vanish.
No period-count root recovery theorem is used in this argument. The alternative
period proof remains available in `BranchRecovery`.

The endpoints `tree_root_unique` and `isTreeRoot_iff_degree` use the literal
intrinsic tree and root predicates. Once the root and a point in its one-slice
are fixed, `treeRoot_children_determined` identifies both children and both
essential spaces by restriction.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open BooleanFunctions
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]

set_option backward.isDefEq.respectTransparency false
/-- Lemma 6.5's degree characterization for any literal root data.
The forward implication uses separated top-degree monomials in adapted
`s,x,y,z` coordinates; the reverse implication is `sφ=sφ₁`. -/
theorem IsTreeRoot.degree_characterization {h : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot h φ s)
    (ℓ : Module.Dual (ZMod 2) U) (hℓ : ℓ≠0) :
    vectorDegree (fun x => ℓ x*φ x)≤h ↔ ℓ=s := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  letI := templateSpaceAddCommGroup n
  letI := templateSpaceModule n
  letI := templateSpaceFintype n
  obtain ⟨a,ha,hsel,hφ⟩ := hs.coordinates
  rw [hφ]
  exact root_degree_characterization_affinePullback
    (V := TemplateSpace n) (W := TemplateSpace n) (template n) (template n)
    a ha s hsel ℓ hℓ (by omega : 2≤n+2)
    (template_vectorDegree n) (template_vectorDegree n)

/-- The root itself has a product of degree at most the tree height. -/
theorem IsTreeRoot.degree_mul_le {h : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot h φ s) :
    vectorDegree (fun x => s x*φ x)≤h := by
  exact (hs.degree_characterization s hs.nonzero).mpr rfl

/-- Lemma 6.5: any two literal roots coincide, by the degree route. -/
theorem IsTreeRoot.unique {h : ℕ} {φ : U → ZMod 2}
    {s t : Module.Dual (ZMod 2) U} (hs : IsTreeRoot h φ s)
    (ht : IsTreeRoot h φ t) : s=t := by
  exact ((hs.degree_characterization t ht.nonzero).mp ht.degree_mul_le).symm

/-- Every intrinsic tree of height at least three has exactly one root. -/
theorem IsTreeFunction.exists_unique_root {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) (hh : 3≤h) : ∃! s, IsTreeRoot h φ s := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hh
  obtain ⟨s,hs⟩ := (isTreeFunction_succ_iff_exists_root n φ).mp hφ
  exact ⟨s,hs,fun t ht => ht.unique hs⟩

/-- The whole root clause of Lemma 6.5: the unique root is precisely the
nonzero linear functional whose product with the tree has degree at most `h`.
Its children and essential spaces are determined by literal restriction, as
stated in `treeRoot_children_determined`. -/
theorem tree_root_unique {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) (hh : 3≤h) :
    ∃ s, IsTreeRoot h φ s ∧ ∀ ℓ : Module.Dual (ZMod 2) U,
      ℓ≠0 → (vectorDegree (fun x => ℓ x*φ x)≤h ↔ ℓ=s) := by
  obtain ⟨s,hs,_⟩ := hφ.exists_unique_root hh
  exact ⟨s,hs,fun ℓ hℓ => hs.degree_characterization ℓ hℓ⟩

/-- Recognize literal roots using only nonzeroness and the degree condition. -/
theorem isTreeRoot_iff_degree {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) (hh : 3≤h) (ℓ : Module.Dual (ZMod 2) U) :
    IsTreeRoot h φ ℓ ↔ ℓ≠0 ∧ vectorDegree (fun x => ℓ x*φ x)≤h := by
  constructor
  · intro hℓ
    exact ⟨hℓ.nonzero,hℓ.degree_mul_le⟩
  · rintro ⟨hℓ,hdegree⟩
    obtain ⟨s,hs,hchar⟩ := tree_root_unique hφ hh
    rwa [(hchar ℓ hℓ).mp hdegree]

end BinaryFieldCounterexamples.Trees
