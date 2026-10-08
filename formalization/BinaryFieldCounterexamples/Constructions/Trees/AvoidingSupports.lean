/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingFamily
public import BinaryFieldCounterexamples.Constructions.Trees.SupportFamily
/-!
# Canonical avoiding tree support data

The actual finite avoiding support family preserves exact cardinality, balance, prescribed-subspace disjointness, and the unrestricted tree leaf geometry.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
/-- Actual distinct tree supports avoiding the prescribed subspace. -/
noncomputable def avoidingTreeSupportFamily (n : ℕ) (W : Submodule (ZMod 2) V) : Finset (Finset V) := by
  classical
  exact (avoidingTreeFamily n W).toFinset.image binarySupport
/-- Literal support conversion preserves the exact avoiding family cardinality. -/
theorem avoidingTreeSupportFamily_card (n : ℕ) (W : Submodule (ZMod 2) V) :
    (avoidingTreeSupportFamily n W).card=Nat.card (avoidingTreeFamily n W) := by
  classical
  rw [avoidingTreeSupportFamily,Finset.card_image_of_injective _ binarySupport_injective,
    Set.toFinset_card,Nat.card_eq_fintype_card]
/-- Every avoiding support retains its actual surjective frame witness. -/
theorem mem_avoidingTreeSupportFamily (n : ℕ) (W : Submodule (ZMod 2) V) (S : Finset V) :
    S ∈ avoidingTreeSupportFamily n W ↔ ∃ L : V →ₗ[ZMod 2] TemplateSpace n,
      Function.Surjective L ∧ avoidingTreeFrameProperty n W L ∧
      S=binarySupport (fun x => template n (L x)) := by
  classical
  constructor
  · intro h
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨L,hL,hcore,rfl⟩ := (mem_avoidingTreeFamily_iff n W f).mp (Set.mem_toFinset.mp hf)
    exact ⟨L,hL,hcore,rfl⟩
  · rintro ⟨L,hL,hcore,rfl⟩
    exact Finset.mem_image.mpr ⟨_,Set.mem_toFinset.mpr
      ((mem_avoidingTreeFamily_iff n W _).mpr ⟨L,hL,hcore,rfl⟩),rfl⟩
/-- The constrained supports belong to the actual unrestricted tree family. -/
theorem avoidingTreeSupportFamily_subset (n : ℕ) (W : Submodule (ZMod 2) V) :
    avoidingTreeSupportFamily n W ⊆ treeSupportFamily V n := by
  intro S hS
  obtain ⟨L,hL,_,hS⟩ := (mem_avoidingTreeSupportFamily n W S).mp hS
  exact (mem_treeSupportFamily n S).mpr ⟨L.toAffineMap,hL,hS⟩
/-- Every constrained support is disjoint from the actual prescribed subspace. -/
theorem avoidingTreeSupportFamily_disjoint (n : ℕ) (W : Submodule (ZMod 2) V)
    (S : Finset V) (hS : S ∈ avoidingTreeSupportFamily n W) : ∀ x ∈ S, x ∉ W := by
  classical
  obtain ⟨L,hL,hcore,rfl⟩ := (mem_avoidingTreeSupportFamily n W S).mp hS
  intro x hx hW
  have h1 : template n (L x)=1 := (Finset.mem_filter.mp hx).2
  have h0 := templateAvoidingCore_zero n (L x) (hcore ⟨x,hW⟩)
  exact zero_ne_one (h0.symm.trans h1)
/-- Every avoiding support is exactly balanced on the prescribed ambient space. -/
theorem avoidingTreeSupportFamily_balanced (n : ℕ) (W : Submodule (ZMod 2) V)
    (S : Finset V) (hS : S ∈ avoidingTreeSupportFamily n W) : 2*S.card=Fintype.card V := by
  exact treeSupportFamily_balanced n S (avoidingTreeSupportFamily_subset n W hS)
end BinaryFieldCounterexamples.Trees
