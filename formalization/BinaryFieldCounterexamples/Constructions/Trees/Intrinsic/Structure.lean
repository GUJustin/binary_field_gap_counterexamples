/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Bridge
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Quotient
public import BinaryFieldCounterexamples.Constructions.Trees.SupportFamily
/-!
# Degree-free structure of intrinsic tree functions

The assertions below are the degree-free clauses of Lemma 6.4, Section 6.2:
balance, essential dimension `2^h-1`, disjoint affine leaves of codimension `h`,
affine invariance, complementation, and equivalence after quotienting by any
subspace of periods. They concern Definition 6.3's intrinsic predicate, via
its proved equivalence with the existing surjective affine templates.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
  [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]

/-- An intrinsic tree admits literal surjective affine template coordinates,
and every such representation is an intrinsic tree. -/
theorem isTreeFunction_iff_exists_surjective_affine (n : ℕ) (f : V → ZMod 2) :
    IsTreeFunction (n+2) f ↔ ∃ a : V →ᵃ[ZMod 2] TemplateSpace n,
      Function.Surjective a ∧ f=(fun x => template n (a x)) := by
  rw [isTreeFunction_iff_affinePullbackFamily]
  constructor
  · rintro ⟨⟨a,ha⟩,he⟩; exact ⟨a,ha,he.symm⟩
  · rintro ⟨a,ha,he⟩; exact ⟨⟨a,ha⟩,he.symm⟩

/-- The existing support-family API applies precisely to intrinsic tree functions. -/
theorem binarySupport_mem_treeSupportFamily_iff (n : ℕ) (f : V → ZMod 2) :
    binarySupport f ∈ treeSupportFamily V n ↔ IsTreeFunction (n+2) f := by
  rw [mem_treeSupportFamily,isTreeFunction_iff_exists_surjective_affine]
  constructor
  · rintro ⟨a,ha,he⟩; exact ⟨a,ha,binarySupport_injective he⟩
  · rintro ⟨a,ha,rfl⟩; exact ⟨a,ha,rfl⟩

/-- Lemma 6.4(1): every intrinsic tree is exactly balanced. -/
theorem IsTreeFunction.balanced {h : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction h f) : IsBalanced f := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hf.two_le
  obtain ⟨⟨a,ha⟩,rfl⟩ := (isTreeFunction_iff_affinePullbackFamily n f).mp hf
  intro b
  simpa only [Nat.card_eq_fintype_card] using template_affine_pullback_balanced n a ha b

/-- Lemma 6.4(1): the essential dimension counts all independent tests in the tree. -/
theorem IsTreeFunction.essentialDimension {h : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction h f) : essentialDimension f=2^h-1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hf.two_le
  obtain ⟨⟨a,ha⟩,rfl⟩ := (isTreeFunction_iff_affinePullbackFamily n f).mp hf
  rw [essentialDimension_affineMap_precompose_periodFree (template n)
    (template_period_iff n) a ha,templateSpace_finrank]

/-- The ambient space has room for all essential coordinates of an intrinsic tree. -/
theorem IsTreeFunction.essentialDimension_le_finrank {h : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction h f) : 2^h-1≤Module.finrank (ZMod 2) V := by
  rw [←hf.essentialDimension]
  exact Trees.essentialDimension_le_finrank f

/-- Tree height is at most the ambient dimension, so the affine codimension is literal. -/
theorem IsTreeFunction.height_le_finrank {h : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction h f) : h≤Module.finrank (ZMod 2) V := by
  have hp : h<2^h := Nat.lt_two_pow_self
  have hd := hf.essentialDimension_le_finrank
  omega

/-- Lemma 6.4(1): a height `n+2` support is the disjoint union of `2^(n+1)`
nonempty affine flats, each of codimension `n+2` in the actual domain. -/
theorem IsTreeFunction.flats {n : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction (n+2) f) :
    ∃ A : (Fin (n+1) → ZMod 2) → AffineSubspace (ZMod 2) V,
      {x : V | f x=1}=⋃ i, (A i : Set V) ∧
      Pairwise (fun i j => Disjoint (A i : Set V) (A j : Set V)) ∧
      ∀ i, (A i : Set V).Nonempty ∧
        Module.finrank (ZMod 2) (A i).direction=Module.finrank (ZMod 2) V-(n+2) ∧
        Module.finrank (ZMod 2) (A i).direction+(n+2)=Module.finrank (ZMod 2) V ∧
        Nat.card (A i)=2^(Module.finrank (ZMod 2) V-(n+2)) := by
  have hd := hf.height_le_finrank
  obtain ⟨⟨a,ha⟩,rfl⟩ := (isTreeFunction_iff_affinePullbackFamily n f).mp hf
  refine ⟨fun i => pullbackLeafFlat n a i 1,
    template_pullback_fiber_eq_union n a 1,pullbackLeafFlat_pairwise_disjoint n a 1,?_⟩
  intro i
  have hi := pullbackLeafFlat_direction_finrank n a ha i 1
  exact ⟨(pullbackLeafFlat_direction n a ha i 1).1,hi,
    by rw [hi]; omega,pullbackLeafFlat_card n a ha i 1⟩

/-- Lemma 6.4(2), strengthened to arbitrary surjective affine pullback. -/
theorem IsTreeFunction.affineMap_precompose {h : ℕ} {f : W → ZMod 2}
    (hf : IsTreeFunction h f) (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    IsTreeFunction h (fun x => f (a x)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hf.two_le
  obtain ⟨⟨b,hb⟩,rfl⟩ := (isTreeFunction_iff_affinePullbackFamily n f).mp hf
  apply (isTreeFunction_iff_affinePullbackFamily n _).mpr
  exact ⟨⟨b.comp a,hb.comp ha⟩,rfl⟩

/-- Lemma 6.4(2): invertible affine changes preserve and reflect tree functions. -/
theorem isTreeFunction_affineEquiv_iff (h : ℕ) (f : W → ZMod 2)
    (e : V ≃ᵃ[ZMod 2] W) : IsTreeFunction h (fun x => f (e x)) ↔ IsTreeFunction h f := by
  constructor
  · intro hf
    have hh := hf.affineMap_precompose e.symm.toAffineMap e.symm.surjective
    have he : (fun x => f (e (e.symm.toAffineMap x)))=f := by
      funext x
      exact congrArg f (e.apply_symm_apply x)
    rwa [he] at hh
  · intro hf
    exact hf.affineMap_precompose e.toAffineMap e.surjective

/-- Lemma 6.4(2): adding one complements a tree function. -/
theorem IsTreeFunction.complement {h : ℕ} {f : V → ZMod 2}
    (hf : IsTreeFunction h f) : IsTreeFunction h (fun x => f x+1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hf.two_le
  exact (isTreeFunction_iff_affinePullbackFamily n _).mpr
    (affinePullbackFamily_template_complement n f
      ((isTreeFunction_iff_affinePullbackFamily n f).mp hf))

/-- Lemma 6.4(3): quotienting by ignored directions preserves and reflects the
intrinsic tree predicate. The induced function is constructed from `hP`. -/
theorem isTreeFunction_quotient_iff (h : ℕ) (f : V → ZMod 2)
    (P : Submodule (ZMod 2) V) (hP : P ≤ periodSubmodule f) :
    IsTreeFunction h f ↔ IsTreeFunction h (quotientFunction f P hP) := by
  letI : Fintype (V ⧸ P) := Fintype.ofFinite _
  by_cases hh : 2≤h
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hh
    rw [isTreeFunction_iff_affinePullbackFamily,isTreeFunction_iff_affinePullbackFamily]
    exact affinePullbackFamily_quotient_iff n f P hP
  · exact ⟨fun hf => (hh hf.two_le).elim,fun hf => (hh hf.two_le).elim⟩

end BinaryFieldCounterexamples.Trees
