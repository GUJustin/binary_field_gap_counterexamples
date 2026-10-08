/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
public import BinaryFieldCounterexamples.Constructions.Trees.PullbackProperties
/-!
# Distinct finite tree-support families

The family consists of literal supports of all surjective affine pullbacks.
Binary functions are recovered by their supports, so the finite family has
exactly the function-family cardinality. Every support is balanced and has
the proved disjoint affine-flat decomposition. Complementation remains inside
the family and gives exact half incidence at each point of the domain.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Literal finite support of a binary function. -/
noncomputable def binarySupport {V : Type*} [Fintype V] (f : V → ZMod 2) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => f x=1)
/-- Binary functions are uniquely determined by their literal supports. -/
theorem binarySupport_injective {V : Type*} [Fintype V] : Function.Injective (binarySupport (V := V)) := by
  classical
  intro f g h
  funext x
  have hx : f x=1 ↔ g x=1 := by
    have hm := congrArg (fun S : Finset V => x ∈ S) h
    simpa [binarySupport] using hm
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (f x) with hf|hf <;>
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (g x) with hg|hg <;> simp_all
/-- The actual finite family of distinct balanced tree supports on a prescribed space. -/
noncomputable def treeSupportFamily (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) : Finset (Finset V) := by
  classical
  exact (affinePullbackFamily V (template n)).toFinset.image binarySupport
/-- Every family member comes from a literal surjective affine template map, and conversely. -/
theorem mem_treeSupportFamily {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (S : Finset V) : S ∈ treeSupportFamily V n ↔
      ∃ a : V →ᵃ[ZMod 2] TemplateSpace n, Function.Surjective a ∧ S=binarySupport (fun x => template n (a x)) := by
  classical
  constructor
  · intro h
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp h
    have hf' : f ∈ affinePullbackFamily V (template n) := Set.mem_toFinset.mp hf
    obtain ⟨a,rfl⟩ := hf'
    exact ⟨a.1,a.2,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact Finset.mem_image.mpr ⟨_,Set.mem_toFinset.mpr ⟨⟨a,ha⟩,rfl⟩,rfl⟩
/-- No support is counted twice when passing from actual binary functions to sets. -/
theorem treeSupportFamily_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) : (treeSupportFamily V n).card=Nat.card (affinePullbackFamily V (template n)) := by
  classical
  rw [treeSupportFamily,Finset.card_image_of_injective _ binarySupport_injective,Set.toFinset_card,Nat.card_eq_fintype_card]
/-- Every counted support contains exactly half the prescribed domain. -/
theorem treeSupportFamily_balanced {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (S : Finset V) (hS : S ∈ treeSupportFamily V n) : 2*S.card=Fintype.card V := by
  classical
  obtain ⟨a,ha,rfl⟩ := (mem_treeSupportFamily n S).mp hS
  simpa only [binarySupport,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    template_affine_pullback_balanced n a ha 1
/-- Template complementation remains inside the literal affine pullback family. -/
theorem affinePullbackFamily_template_complement {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (f : V → ZMod 2) (hf : f ∈ affinePullbackFamily V (template n)) :
    (fun x => f x+1) ∈ affinePullbackFamily V (template n) := by
  obtain ⟨a,rfl⟩ := hf
  let e := AffineEquiv.constVAdd (ZMod 2) (TemplateSpace n) (templateComplementVector n)
  refine ⟨⟨e.toAffineMap.comp a.1,e.surjective.comp a.2⟩,?_⟩
  funext x
  change template n (templateComplementVector n+a.1 x)=template n (a.1 x)+1
  rw [add_comm,template_add_complementVector]
/-- The finite family is closed under taking the complementary subset of the domain. -/
theorem treeSupportFamily_complement {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (S : Finset V) (hS : S ∈ treeSupportFamily V n) :
    Finset.univ \ S ∈ treeSupportFamily V n := by
  classical
  obtain ⟨a,ha,rfl⟩ := (mem_treeSupportFamily n S).mp hS
  have hc := affinePullbackFamily_template_complement n (fun x => template n (a x)) ⟨⟨a,ha⟩,rfl⟩
  have hs : Finset.univ \ binarySupport (fun x => template n (a x))=
      binarySupport (fun x => template n (a x)+1) := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,binarySupport,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (template n (a x)) with h|h <;>
      simp [h,show (1:ZMod 2)+1=0 by decide]
  rw [hs]
  exact Finset.mem_image.mpr ⟨_,Set.mem_toFinset.mpr hc,rfl⟩
/-- Complementation pairs supports through and away from every point exactly. -/
theorem treeSupportFamily_point_incidence {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (x : V) :
    2*((treeSupportFamily V n).filter (fun S => x ∈ S)).card=(treeSupportFamily V n).card := by
  classical
  let F := treeSupportFamily V n
  have he : (F.filter fun S => x ∈ S).card=(F.filter fun S => x ∉ S).card := by
    apply Finset.card_bij (fun S _ => Finset.univ \ S)
    · intro S hS
      obtain ⟨hSF,hx⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨treeSupportFamily_complement n S hSF,by simp [hx]⟩
    · intro S hS T hT h
      have hh := congrArg (fun S : Finset V => Finset.univ \ S) h
      simpa using hh
    · intro S hS
      obtain ⟨hSF,hx⟩ := Finset.mem_filter.mp hS
      refine ⟨Finset.univ \ S,Finset.mem_filter.mpr ⟨treeSupportFamily_complement n S hSF,by simp [hx]⟩,?_⟩
      simp
  have ht := Finset.card_filter_add_card_filter_not (s := F) (p := fun S => x ∈ S)
  change 2*(F.filter (fun S => x ∈ S)).card=F.card
  omega
/-- Every counted support has the exact disjoint affine-flat decomposition used by its locator. -/
theorem treeSupportFamily_flats {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (S : Finset V) (hS : S ∈ treeSupportFamily V n) :
    ∃ A : (Fin (n+1) → ZMod 2) → AffineSubspace (ZMod 2) V,
      (S:Set V)=⋃ i, (A i:Set V) ∧
      Pairwise (fun i j => Disjoint (A i:Set V) (A j:Set V)) ∧
      ∀ i, (A i:Set V).Nonempty ∧ Nat.card (A i)=2^(Module.finrank (ZMod 2) V-(n+2)) := by
  obtain ⟨a,ha,rfl⟩ := (mem_treeSupportFamily n S).mp hS
  refine ⟨fun i => pullbackLeafFlat n a i 1,?_,pullbackLeafFlat_pairwise_disjoint n a 1,?_⟩
  · rw [←template_pullback_fiber_eq_union]
    ext x
    simp [binarySupport]
  · intro i
    exact ⟨(pullbackLeafFlat_direction n a ha i 1).1,pullbackLeafFlat_card n a ha i 1⟩
end BinaryFieldCounterexamples.Trees
