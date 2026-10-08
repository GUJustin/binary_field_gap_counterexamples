/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.RootData
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Counts
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBranch
/-!
# Degree and the complete structure of intrinsic trees

[Lemma 6.4](../../../../../binary-field-counterexamples.pdf#page=60), in
Section 6.2, states balance, exact degree, essential dimension, affine leaves,
affine closure, complementation, quotient invariance, and the base count 56.
This module completes the degree clauses and exposes the whole structure
statement through `tree_structure` and `tree_quotient_structure`, alongside
the imported closure and count endpoints.

The degree induction uses independent child coordinates: the leading part is
`s(Ω₀+Ω₁)`, so branching raises the degree by one. The public statements concern
`IsTreeFunction`, whose base case literally has the paper's degree-two clause.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open BooleanFunctions
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]

/-- Independent branching raises the exact degree by one at each level.
This is the degree induction in Lemma 6.4(1), in minimal coordinates. -/
theorem template_vectorDegree (n : ℕ) : vectorDegree (template n)=n+2 := by
  induction n with
  | zero =>
    have h := isHeightTwoTree_affinePullback
      (AffineMap.id (ZMod 2) (Fin 3 → ZMod 2)) Function.surjective_id
    exact h.2.1
  | succ n ih =>
    change vectorDegree (branch (template n) (template n))=n+1+2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      vectorDegree_branch (template n) (template n) (by omega : 0<n+2) ih ih.le

/-- Lemma 6.4(1): every literal height-`h` tree function has ANF degree `h`.
The proof uses the independent-branch leading monomial, followed by the
surjective affine invariance of Boolean degree. -/
theorem IsTreeFunction.degree {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) : vectorDegree φ=h := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hφ.two_le
  obtain ⟨a,ha,rfl⟩ := (isTreeFunction_iff_exists_surjective_affine n φ).mp hφ
  exact (vectorDegree_comp_affine_of_surjective (template n) a ha).trans
    (template_vectorDegree n)

/-- Passing to the actual quotient by any subspace of periods preserves the
ANF degree, for every Boolean function, not only trees (Lemma 6.4(3)). -/
theorem vectorDegree_quotientFunction (φ : U → ZMod 2)
    (P : Submodule (ZMod 2) U) (hP : P≤periodSubmodule φ) :
    vectorDegree (quotientFunction φ P hP)=vectorDegree φ := by
  have h := vectorDegree_comp_affine_of_surjective (quotientFunction φ P hP)
    P.mkQ.toAffineMap P.mkQ_surjective
  exact h.symm

/-- Uniform fibers of a surjective affine map preserve and reflect exact
balance; this includes all period quotients, even a zero-dimensional quotient. -/
theorem isBalanced_affineMap_precompose_iff {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Fintype W] (φ : W → ZMod 2)
    (a : U →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    IsBalanced (fun x => φ (a x)) ↔ IsBalanced φ := by
  have hc := affine_preimage_fiber_count a ha φ
  have hu : 0<Fintype.card U := Fintype.card_pos
  have hw : 0<Fintype.card W := Fintype.card_pos
  constructor
  · intro hb b
    have h := hc b
    have hb' := hb b
    simp only [Nat.card_eq_fintype_card] at h hb' ⊢
    nlinarith
  · intro hb b
    have h := hc b
    have hb' := hb b
    simp only [Nat.card_eq_fintype_card] at h hb' ⊢
    nlinarith

/-- Lemma 6.4(3), including the degree, essential-dimension, and balance
invariants used in the paper's proof. The quotient function is the literal
function induced by `φ`, and no dimension or positivity hypothesis is added. -/
theorem tree_quotient_structure (h : ℕ) (φ : U → ZMod 2)
    (P : Submodule (ZMod 2) U) (hP : P≤periodSubmodule φ) :
    vectorDegree (quotientFunction φ P hP)=vectorDegree φ ∧
    essentialDimension (quotientFunction φ P hP)=essentialDimension φ ∧
    (IsBalanced (quotientFunction φ P hP) ↔ IsBalanced φ) ∧
    (IsTreeFunction h φ ↔ IsTreeFunction h (quotientFunction φ P hP)) := by
  letI : Fintype (U ⧸ P) := Fintype.ofFinite _
  let g := quotientFunction φ P hP
  have he : (fun x => g (P.mkQ.toAffineMap x))=φ := by rfl
  have hE := essentialDimension_affineMap_precompose g P.mkQ.toAffineMap P.mkQ_surjective
  rw [he] at hE
  have hB := isBalanced_affineMap_precompose_iff g P.mkQ.toAffineMap P.mkQ_surjective
  rw [he] at hB
  exact ⟨vectorDegree_quotientFunction φ P hP,hE.symm,hB.symm,
    isTreeFunction_quotient_iff h φ P hP⟩

/-- Lemma 6.4(1), as one paper-facing contract: balance, exact degree,
essential dimension, and exactly `2^(h-1)` disjoint affine flats of codimension
`h`. Here actual height is `n+2`, and `Fin (n+1) → F₂` indexes the flats.
Together with `isTreeFunction_affineEquiv_iff`, `IsTreeFunction.complement`,
`isTreeFunction_quotient_iff`, `vectorDegree_quotientFunction`, and
`isTreeFunction_two_count`, this gives all four clauses of Lemma 6.4. -/
theorem tree_structure (n : ℕ) (φ : U → ZMod 2)
    (hφ : IsTreeFunction (n+2) φ) :
    IsBalanced φ ∧ vectorDegree φ=n+2 ∧ essentialDimension φ=2^(n+2)-1 ∧
    ∃ A : (Fin (n+1) → ZMod 2) → AffineSubspace (ZMod 2) U,
      {x : U | φ x=1}=⋃ i, (A i : Set U) ∧
      Pairwise (fun i j => Disjoint (A i : Set U) (A j : Set U)) ∧
      ∀ i, (A i : Set U).Nonempty ∧
        Module.finrank (ZMod 2) (A i).direction=Module.finrank (ZMod 2) U-(n+2) ∧
        Module.finrank (ZMod 2) (A i).direction+(n+2)=Module.finrank (ZMod 2) U ∧
        Nat.card (A i)=2^(Module.finrank (ZMod 2) U-(n+2)) := by
  exact ⟨hφ.balanced,hφ.degree,hφ.essentialDimension,hφ.flats⟩

/-- Lemma 6.4(1) at the literal height in Definition 6.3. The support has
exactly `2^(h-1)` nonempty, pairwise disjoint affine leaves of codimension `h`.
The other clauses are the affine and complement closure endpoints in
`Structure`, `tree_quotient_structure`, and `isTreeFunction_two_count`. -/
theorem IsTreeFunction.structure {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) :
    IsBalanced φ ∧ vectorDegree φ=h ∧ Trees.essentialDimension φ=2^h-1 ∧
    ∃ A : (Fin (h-1) → ZMod 2) → AffineSubspace (ZMod 2) U,
      {x : U | φ x=1}=⋃ i, (A i : Set U) ∧
      Pairwise (fun i j => Disjoint (A i : Set U) (A j : Set U)) ∧
      ∀ i, (A i : Set U).Nonempty ∧
        Module.finrank (ZMod 2) (A i).direction=Module.finrank (ZMod 2) U-h ∧
        Module.finrank (ZMod 2) (A i).direction+h=Module.finrank (ZMod 2) U ∧
        Nat.card (A i)=2^(Module.finrank (ZMod 2) U-h) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hφ.two_le
  rw [show n+2-1=n+1 by omega]
  exact tree_structure n φ hφ

end BinaryFieldCounterexamples.Trees
