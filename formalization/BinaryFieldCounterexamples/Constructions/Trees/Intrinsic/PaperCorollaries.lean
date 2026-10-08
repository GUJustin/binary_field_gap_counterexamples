/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Counts
public import BinaryFieldCounterexamples.Constructions.Trees.SupportLocators
public import BinaryFieldCounterexamples.Constructions.Trees.FinitePair
public import BinaryFieldCounterexamples.Constructions.Trees.DomainPair
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingCounts
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingPair
/-!
# Intrinsic statements of the tree-support corollaries

These statements use the tree functions of Definition 6.3, rather than
surjective template presentations. The support locator and finite-pair
corollaries are the construction steps used in Corollary 6.7 and Theorem 6.10
of `sections/constructions/additive-support-trees.tex`. The bridge transfers
the existing quantitative conclusions without changing the collision energy,
the strict message-degree bound, or either input-agreement guarantee.

The selected avoiding family used by the half-rate theorem retains its
canonical avoiding restriction. We prove that every selected member is an
intrinsic tree; we do not identify it with all trees vanishing on the
prescribed subspace.
-/
@[expose] public section
attribute [local instance] Classical.decEq Classical.propDecidable
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Exact balance for supports of the paper's intrinsic trees. -/
theorem IsTreeFunction.binarySupport_card {h : ℕ} {φ : V → ZMod 2}
    (hφ : IsTreeFunction h φ) : 2 * (binarySupport φ).card = Fintype.card V := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hφ.two_le
  exact treeSupportFamily_balanced n _
    ((binarySupport_mem_treeSupportFamily_iff n φ).mpr hφ)

/-- Complementation preserves the intrinsic finite support family. -/
theorem intrinsicTreeSupportFamily_complement (h : ℕ) (S : Finset V)
    (hS : S ∈ intrinsicTreeSupportFamily V h) :
    Finset.univ \ S ∈ intrinsicTreeSupportFamily V h := by
  obtain ⟨φ, hφ, rfl⟩ := (mem_intrinsicTreeSupportFamily h S).mp hS
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hφ.two_le
  rw [intrinsicTreeSupportFamily_eq]
  exact treeSupportFamily_complement n _
    ((binarySupport_mem_treeSupportFamily_iff n φ).mpr hφ)

/-- Every support selected by the canonical avoiding construction belongs to
an intrinsic tree, and that tree vanishes on the prescribed subspace. -/
theorem exists_isTreeFunction_of_mem_avoidingTreeSupportFamily (n : ℕ)
    (W : Submodule (ZMod 2) V) (S : Finset V)
    (hS : S ∈ avoidingTreeSupportFamily n W) :
    ∃ φ : V → ZMod 2, IsTreeFunction (n+2) φ ∧ S = binarySupport φ ∧
      ∀ x : W, φ x = 0 := by
  obtain ⟨a, ha, hcore, rfl⟩ := (mem_avoidingTreeSupportFamily n W S).mp hS
  refine ⟨_, (isTreeFunction_iff_affinePullbackFamily n _).mpr
    ⟨⟨a.toAffineMap, ha⟩, rfl⟩, rfl, ?_⟩
  intro x
  exact templateAvoidingCore_zero n (a x) (hcore x)

/-- The existing selected avoiding function family consists of intrinsic trees. -/
theorem isTreeFunction_of_mem_avoidingTreeFamily (n : ℕ)
    (W : Submodule (ZMod 2) V) (φ : V → ZMod 2)
    (hφ : φ ∈ avoidingTreeFamily n W) : IsTreeFunction (n+2) φ := by
  obtain ⟨a, ha, _, rfl⟩ := (mem_avoidingTreeFamily_iff n W φ).mp hφ
  exact (isTreeFunction_iff_affinePullbackFamily n _).mpr ⟨⟨a.toAffineMap, ha⟩, rfl⟩

/-- Counting selected avoiding trees with an explicit intrinsic predicate
counts the same distinct functions as the original selected family. -/
theorem selectedIntrinsicTreeFunction_count (n : ℕ) (W : Submodule (ZMod 2) V) :
    Nat.card {φ : V → ZMod 2 //
      IsTreeFunction (n+2) φ ∧ φ ∈ avoidingTreeFamily n W} =
      (avoidingTreeSupportFamily n W).card := by
  rw [avoidingTreeSupportFamily_card]
  apply Nat.card_congr
  exact (Equiv.refl (V → ZMod 2)).subtypeEquiv
    (fun φ => and_iff_right_of_imp (isTreeFunction_of_mem_avoidingTreeFamily n W φ))

end BinaryFieldCounterexamples.Trees

namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators

/-- The support locator corollary, stated directly for an intrinsic height-`h`
tree on the actual embedded binary domain. -/
theorem exists_isTreeFunction_support_locator
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (h d : ℕ) (hdim : Module.finrank (ZMod 2) V = d) (hd : h+1 ≤ d)
    (e : V →ᵃ[ZMod 2] F) (he : Function.Injective e)
    (φ : V → ZMod 2) (hφ : Trees.IsTreeFunction h φ) :
    ∃ P : F[X], P.Monic ∧ P.natDegree = 2^(d-1) ∧
      (∀ x, P.eval x = 0 ↔ x ∈ (Trees.binarySupport φ).image e) ∧
      (P-X^(2^(d-1))).natDegree ≤ 2^(d-1)-2^(d-(h+1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hφ.two_le
  exact exists_tree_support_locator n d hdim (by omega) e he _
    ((Trees.binarySupport_mem_treeSupportFamily_iff n φ).mpr hφ)

/-- The finite-pair corollary with its population given by the supports of
intrinsic height-`h` functions, counting each support once. -/
theorem exists_pair_of_intrinsic_tree_support_family
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (h d : ℕ) (hh : 2 ≤ h) (hdim : Module.finrank (ZMod 2) V = d)
    (hd : h+1 ≤ d) (hV : Fintype.card V = 2^d)
    (e : V →ᵃ[ZMod 2] F) (he : Function.Injective e) (hq : 2^d < Fintype.card F) :
    let D := Finset.univ.image e
    let T : ℕ := 2^(d-1)
    let K : ℕ := T-2^(d-(h+1))
    let M := (Trees.intrinsicTreeSupportFamily V h).card
    let E : ℚ := (K : ℚ)*M.choose 2-(2^d : ℚ)*(M/2).choose 2
    ∃ u v : D → F, commonAgreementEQ D K u v K ∧ agreementEQ D K v K ∧
      agreementLE D K u (T-1) ∧
      max (M-⌊E/(Fintype.card F-2^d)⌋₊)
        ⌈(Fintype.card F-2^d : ℚ)*M^2/((Fintype.card F-2^d)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges D K u v T).card := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hh
  simpa only [Trees.intrinsicTreeSupportFamily_eq, show n+2+1 = n+3 by omega] using
    exists_pair_of_tree_support_family n d hdim (by omega) hV e he hq

/-- The prescribed-domain population assembly accepts the exact count of
intrinsic tree functions. -/
theorem half_agreement_trees_of_intrinsic_population
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 2 ≤ h) (hd : h+1 ≤ d)
    (hD : (additiveDomain D).card = 2^d) (hq : 2^d < Fintype.card F)
    (hpop : Nat.card {φ : D → ZMod 2 // Trees.IsTreeFunction h φ} = treeSupportCount h d) :
    let N : ℕ := 2^d
    let T : ℕ := N/2
    let K : ℕ := N/2-N/2^(h+1)
    let M : ℕ := treeSupportCount h d
    let E : ℚ := (K : ℚ)*M.choose 2-(N : ℚ)*(M/2).choose 2
    let A := additiveDomain D
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N : ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card := by
  apply half_agreement_trees_of_population D d h hh hd hD hq
  rw [← Trees.intrinsicTreeSupportFamily_card] at hpop
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hh
  subst h
  simpa only [Trees.intrinsicTreeSupportFamily_eq, Nat.add_sub_cancel] using hpop

/-- The padded finite-pair construction counts actual intrinsic functions in
the selected canonical avoiding family. It retains both image bounds and
both individual input-agreement guarantees. -/
theorem exists_pair_of_selected_intrinsic_tree_functions
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (h d : ℕ) (hh : 2 ≤ h) (hdim : Module.finrank (ZMod 2) V = d)
    (hd : h+1 ≤ d) (hV : Fintype.card V = 2^d)
    (W : Submodule (ZMod 2) V) (hW : Nat.card W = 2^(d-(h+1)))
    (e : V →ᵃ[ZMod 2] F) (he : Function.Injective e) (hq : 2^d < Fintype.card F) :
    let D := Finset.univ.image e
    let K : ℕ := 2^(d-1)
    let w : ℕ := 2^(d-(h+1))
    let M := Nat.card {φ : V → ZMod 2 // Trees.IsTreeFunction h φ ∧
      φ ∈ Trees.avoidingTreeFamily (h-2) W}
    let E : ℚ := (((K : ℚ)-w-(K : ℚ)^2/((2^d : ℚ)-w))*M^2+w*M)/2
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (K+w-1) ∧
      max (M-⌊E/(Fintype.card F-2^d)⌋₊)
        ⌈(Fintype.card F-2^d : ℚ)*M^2/((Fintype.card F-2^d)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges D K f g (K+w)).card := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hh

  -- Identify distinct intrinsic functions with the selected support population.
  dsimp only
  rw [Nat.add_sub_cancel, Trees.selectedIntrinsicTreeFunction_count]

  -- Transfer the padded locator construction with the same gap and energy.
  simpa only [show n+2+1 = n+3 by omega] using
    exists_pair_of_avoiding_tree_support_family n d hdim (by omega) hV W
      (by simpa using hW) e he hq

end BinaryFieldCounterexamples
