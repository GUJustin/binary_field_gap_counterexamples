/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingCore
public import BinaryFieldCounterexamples.Constructions.Trees.ConstrainedLinearPullbacks
/-!
# Actual avoiding tree families

Concrete surjective frames map the prescribed subspace into the canonical core. Core invariance proves representation independence and the exact origin-stabilizer count factor for the literal function family.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Actual frames carry the prescribed subspace into the canonical avoiding core. -/
def avoidingTreeFrameProperty (n : ℕ) (W : Submodule (ZMod 2) V)
    (L : V →ₗ[ZMod 2] TemplateSpace n) : Prop := ∀ x : W, templateAvoidingCore n (L x)
/-- The avoiding property of a literal function is witnessed by an actual surjective frame. -/
def avoidingTreeFunctionProperty (n : ℕ) (W : Submodule (ZMod 2) V) (f : V → ZMod 2) : Prop :=
  ∃ L : V →ₗ[ZMod 2] TemplateSpace n, Function.Surjective L ∧
    avoidingTreeFrameProperty n W L ∧ (fun x => template n (L x))=f
/-- Actual distinct canonical avoiding tree functions. -/
def avoidingTreeFamily (n : ℕ) (W : Submodule (ZMod 2) V) : Set (V → ZMod 2) :=
  constrainedLinearPullbackFamily (template n) (avoidingTreeFunctionProperty n W)
/-- The core condition is independent of the chosen actual surjective frame. -/
theorem avoidingTreeFrameProperty_iff (n : ℕ) (W : Submodule (ZMod 2) V)
    (L : V →ₗ[ZMod 2] TemplateSpace n) (hL : Function.Surjective L) :
    avoidingTreeFrameProperty n W L ↔
      avoidingTreeFunctionProperty n W (fun x => template n (L x)) := by
  constructor
  · intro h; exact ⟨L,hL,h,rfl⟩
  · rintro ⟨M,hM,hcore,hfun⟩
    obtain ⟨e,he,_⟩ := existsUnique_stabilizer_of_pullback_eq (template n) (template_period_iff n)
      L.toAffineMap M.toAffineMap hL hM hfun.symm
    change ∀ x : V, e.1 (L x)=M x at he
    have he0 : e.1 0=0 := by simpa using he 0
    intro x
    have h := templateAvoidingCore_stabilizer n e he0 (L x)
    rw [he] at h
    exact h.mp (hcore x)
/-- The actual constrained frame population differs from the family by precisely its origin stabilizer. -/
theorem avoidingTreeFamily_card_mul_stabilizer (n : ℕ) (W : Submodule (ZMod 2) V) :
    Nat.card (avoidingTreeFamily n W)*
      Nat.card {e : affineFunctionStabilizer (template n) // e.1 0=0}=
      Nat.card {L : V →ₗ[ZMod 2] TemplateSpace n // Function.Surjective L ∧
        avoidingTreeFrameProperty n W L} := by
  have h := constrainedLinearPullbackFamily_card_mul_stabilizer (template n) (template_period_iff n)
    (avoidingTreeFunctionProperty n W)
  let e := (Equiv.refl (V →ₗ[ZMod 2] TemplateSpace n)).subtypeEquiv
    (p := fun L : V →ₗ[ZMod 2] TemplateSpace n => Function.Surjective L ∧
      avoidingTreeFunctionProperty n W (fun x => template n (L x)))
    (q := fun L : V →ₗ[ZMod 2] TemplateSpace n => Function.Surjective L ∧ avoidingTreeFrameProperty n W L)
    (fun L => by
      constructor
      · rintro ⟨hL,hP⟩; exact ⟨hL,(avoidingTreeFrameProperty_iff n W L hL).mpr hP⟩
      · rintro ⟨hL,hP⟩; exact ⟨hL,(avoidingTreeFrameProperty_iff n W L hL).mp hP⟩)
  exact h.trans (Nat.card_congr e)
/-- Every function in the actual canonical family vanishes on the prescribed subspace. -/
theorem avoidingTreeFamily_vanishes (n : ℕ) (W : Submodule (ZMod 2) V)
    (f : V → ZMod 2) (hf : f ∈ avoidingTreeFamily n W) (x : W) : f x=0 := by
  obtain ⟨L,rfl⟩ := hf
  have hc := (avoidingTreeFrameProperty_iff n W L.1 L.2.1).mpr L.2.2
  exact templateAvoidingCore_zero n (L.1 x) (hc x)
/-- Membership records an actual surjective frame carrying the prescribed subspace into the core. -/
theorem mem_avoidingTreeFamily_iff (n : ℕ) (W : Submodule (ZMod 2) V) (f : V → ZMod 2) :
    f ∈ avoidingTreeFamily n W ↔ ∃ L : V →ₗ[ZMod 2] TemplateSpace n,
      Function.Surjective L ∧ avoidingTreeFrameProperty n W L ∧ (fun x => template n (L x))=f := by
  constructor
  · rintro ⟨L,rfl⟩
    exact ⟨L.1,L.2.1,(avoidingTreeFrameProperty_iff n W L.1 L.2.1).mpr L.2.2,rfl⟩
  · rintro ⟨L,hL,hcore,rfl⟩
    exact ⟨⟨L,hL,(avoidingTreeFrameProperty_iff n W L hL).mp hcore⟩,rfl⟩
end BinaryFieldCounterexamples.Trees
