/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Structure
public import BinaryFieldCounterexamples.Constructions.Trees.FrameArithmetic
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.CountRecurrence
public import BinaryFieldCounterexamples.Counting.TreeWholeGrowth
/-!
# Counts and incidences for the intrinsic tree predicate

Lemma 6.6 in Section 6.2 counts functions defined intrinsically in Definition
6.3. The intrinsic/template bridge identifies their literal supports with the
existing counted template family. Thus the exact product `B_h(d)`, its Gaussian
factorization, and exact half incidence concern the paper's predicate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The literal finite family of supports of intrinsic height-`h` tree functions. -/
noncomputable def intrinsicTreeSupportFamily (V : Type*) [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (h : ℕ) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter (IsTreeFunction h)).image binarySupport

/-- Membership retains the actual intrinsic Boolean function. -/
theorem mem_intrinsicTreeSupportFamily (h : ℕ) (S : Finset V) :
    S ∈ intrinsicTreeSupportFamily V h ↔
      ∃ f : V → ZMod 2, IsTreeFunction h f ∧ S=binarySupport f := by
  classical
  simp only [intrinsicTreeSupportFamily,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨f,hf,he⟩; exact ⟨f,hf,he.symm⟩
  · rintro ⟨f,hf,he⟩; exact ⟨f,hf,he.symm⟩

/-- The bridge identifies the literal support families, with no multiplicity. -/
theorem intrinsicTreeSupportFamily_eq (n : ℕ) :
    intrinsicTreeSupportFamily V (n+2)=treeSupportFamily V n := by
  ext S
  rw [mem_intrinsicTreeSupportFamily,mem_treeSupportFamily]
  constructor
  · rintro ⟨f,hf,rfl⟩
    obtain ⟨⟨a,ha⟩,rfl⟩ := (isTreeFunction_iff_affinePullbackFamily n f).mp hf
    exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨_,(isTreeFunction_iff_affinePullbackFamily n _).mpr ⟨⟨a,ha⟩,rfl⟩,rfl⟩

/-- Supports and intrinsic Boolean functions have exactly the same count. -/
theorem intrinsicTreeSupportFamily_card (h : ℕ) :
    (intrinsicTreeSupportFamily V h).card=Nat.card {f : V → ZMod 2 // IsTreeFunction h f} := by
  classical
  rw [intrinsicTreeSupportFamily,Finset.card_image_of_injective _ binarySupport_injective]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Lemma 6.6: the number `B_h(d)` of intrinsic tree functions is the exact
existing manuscript product, for every admissible dimension. -/
theorem isTreeFunction_count (n : ℕ) (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) V) :
    Nat.card {f : V → ZMod 2 // IsTreeFunction (n+2) f}=
      treeSupportCount (n+2) (Module.finrank (ZMod 2) V) := by
  rw [←intrinsicTreeSupportFamily_card,intrinsicTreeSupportFamily_eq]
  exact treeSupportFamily_card_eq n hd

/-- Lemma 6.6: `B_h(d)=[d choose t_h]_2 C_h`, with the minimal-space count
`C_h=treeSupportCount h (2^h-1)`. -/
theorem isTreeFunction_count_gaussian (n : ℕ)
    (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) V) :
    Nat.card {f : V → ZMod 2 // IsTreeFunction (n+2) f}=
      gaussianBinomial 2 (Module.finrank (ZMod 2) V) (2^(n+2)-1)*
        treeSupportCount (n+2) (2^(n+2)-1) := by
  rw [isTreeFunction_count n hd]
  exact treeSupportCount_eq_gaussian_mul n _ hd

/-- Lemma 6.4(4): exactly 56 intrinsic height-two functions occur in dimension three. -/
theorem isTreeFunction_two_count (hd : Module.finrank (ZMod 2) V=3) :
    Nat.card {f : V → ZMod 2 // IsTreeFunction 2 f}=56 := by
  exact isHeightTwoTree_card_dimension_three hd

/-- Lemma 6.6: every point belongs to exactly half the intrinsic tree supports. -/
theorem intrinsicTreeSupportFamily_point_incidence (n : ℕ) (x : V) :
    2*((intrinsicTreeSupportFamily V (n+2)).filter (fun S => x ∈ S)).card=
      (intrinsicTreeSupportFamily V (n+2)).card := by
  rw [intrinsicTreeSupportFamily_eq]
  exact treeSupportFamily_point_incidence n x

/-- The intrinsic counts have the paper's fixed-height order of growth. -/
theorem intrinsicTreeSupportCount_growth (h : ℕ) (hh : 2≤h) :
    HasBinaryPowerGrowth (treeSupportCount h) (2^h-1) := by
  exact treeSupportCount_growth h hh

end BinaryFieldCounterexamples.Trees
