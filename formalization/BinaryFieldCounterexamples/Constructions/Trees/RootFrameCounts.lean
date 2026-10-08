/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.RootFrames
/-!
# Exact fixed-root frame counts

The root-coordinate decomposition and the uniform joint-surjection count give
the exact number of surjective frames satisfying an arbitrary predicate on the
restricted left child map.
-/
@[expose] public section

namespace BinaryFieldCounterexamples.Trees
set_option maxHeartbeats 800000

variable {V T : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup T] [Module (ZMod 2) T] [Finite V] [Finite T]



/-- Surjective fixed-root frames satisfying a predicate on the left restriction. -/
def RootAdmissibleFrames (z : V →ₗ[ZMod 2] ZMod 2)
    (P : (LinearMap.ker z →ₗ[ZMod 2] T) → Prop) :=
  {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) //
    Function.Surjective L ∧ rootFirst L=z ∧ P (rootRestrictedLeft z L)}

/-- Repackage an admissible frame as a frame with its fixed-root proof bundled first. -/
noncomputable def rootAdmissibleFixedEquiv (z : V →ₗ[ZMod 2] ZMod 2)
    (P : (LinearMap.ker z →ₗ[ZMod 2] T) → Prop) :
    RootAdmissibleFrames z P ≃
      {L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z} //
        Function.Surjective L.1 ∧ P (rootRestrictedLeft z L.1)} := {
  toFun := fun L => ⟨⟨L.1,L.2.2.1⟩,L.2.1,L.2.2.2⟩
  invFun := fun L => ⟨L.1.1,L.2.1,L.1.2,L.2.2⟩
  left_inv := by intro L; rfl
  right_inv := by intro L; rfl }

/-- Admissible frames in restricted-child and root-value coordinates. -/
noncomputable def rootAdmissibleComponentsEquiv (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z) (P : (LinearMap.ker z →ₗ[ZMod 2] T) → Prop) :
    RootAdmissibleFrames z P ≃
      {C : (((LinearMap.ker z →ₗ[ZMod 2] T) × T) ×
        ((LinearMap.ker z →ₗ[ZMod 2] T) × T)) //
        Function.Surjective (C.1.1.prod C.2.1) ∧ P C.1.1} :=
  (rootAdmissibleFixedEquiv z P).trans
    ((rootFrameComponentsEquiv z hz).subtypeEquiv
      (p := fun L => Function.Surjective L.1 ∧ P (rootRestrictedLeft z L.1))
      (q := fun C => Function.Surjective (C.1.1.prod C.2.1) ∧ P C.1.1)
      (fun L => and_congr (rootFrame_surjective_iff z hz L)
        (by rw [rootFrameComponents_left z hz L])))

/-- A subtype of a product with constant finite fibers has product cardinality. -/
theorem card_subtype_prod_of_constant_fibers
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : A → Prop) (R : A → B → Prop) [DecidablePred Q]
    [∀a, DecidablePred (R a)] (C : ℕ)
    (hcard : ∀a, Q a → Nat.card {b : B // R a b}=C) :
    Nat.card {p : A×B // Q p.1 ∧ R p.1 p.2}=
      Nat.card {a : A // Q a}*C := by
  let E : {p : A×B // Q p.1 ∧ R p.1 p.2} ≃
      Σ a : {a : A // Q a}, {b : B // R a.1 b} := {
    toFun := fun p => ⟨⟨p.1.1,p.2.1⟩,⟨p.1.2,p.2.2⟩⟩
    invFun := fun p => ⟨(p.1.1,p.2.1),p.1.2,p.2.2⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }
  rw [Nat.card_congr E,Nat.card_sigma]
  simp_rw [hcard _ (Subtype.property _)]
  simp


/-- Reassociate root components so the left restricted map is the outer coordinate. -/
noncomputable def rootComponentsReassocEquiv (z : V →ₗ[ZMod 2] ZMod 2)
    (P : (LinearMap.ker z →ₗ[ZMod 2] T) → Prop) :
    {C : (((LinearMap.ker z →ₗ[ZMod 2] T) × T) ×
      ((LinearMap.ker z →ₗ[ZMod 2] T) × T)) //
      Function.Surjective (C.1.1.prod C.2.1) ∧ P C.1.1} ≃
    {p : (LinearMap.ker z →ₗ[ZMod 2] T) ×
      ((LinearMap.ker z →ₗ[ZMod 2] T) × T × T) //
      (Function.Surjective p.1 ∧ P p.1) ∧
        Function.Surjective (p.1.prod p.2.1)} := by
  let E : (((LinearMap.ker z →ₗ[ZMod 2] T) × T) ×
      ((LinearMap.ker z →ₗ[ZMod 2] T) × T)) ≃
      (LinearMap.ker z →ₗ[ZMod 2] T) ×
        ((LinearMap.ker z →ₗ[ZMod 2] T) × T × T) := {
    toFun := fun C => (C.1.1,C.2.1,C.1.2,C.2.2)
    invFun := fun p => ((p.1,p.2.2.1),(p.2.1,p.2.2.2))
    left_inv := by intro C; rfl
    right_inv := by intro p; rfl }
  exact E.subtypeEquiv
    (p := fun C => Function.Surjective (C.1.1.prod C.2.1) ∧ P C.1.1)
    (q := fun p => (Function.Surjective p.1 ∧ P p.1) ∧
      Function.Surjective (p.1.prod p.2.1))
    (fun C => by
      constructor
      · intro h
        have hleft : Function.Surjective C.1.1 := by
          intro u
          obtain ⟨x,hx⟩ := h.1 (u,0)
          exact ⟨x,congrArg Prod.fst hx⟩
        exact ⟨⟨hleft,h.2⟩,h.1⟩
      · intro h
        exact ⟨h.2,h.1.2⟩)

/-- Root values split off from the jointly-surjective right-map fiber. -/
noncomputable def rootFiberEquiv (z : V →ₗ[ZMod 2] ZMod 2)
    (A : LinearMap.ker z →ₗ[ZMod 2] T) :
    {p : (LinearMap.ker z →ₗ[ZMod 2] T) × T × T //
      Function.Surjective (A.prod p.1)} ≃
      ({B : LinearMap.ker z →ₗ[ZMod 2] T // Function.Surjective (A.prod B)} × T × T) := {
  toFun := fun p => (⟨p.1.1,p.2⟩,p.1.2.1,p.1.2.2)
  invFun := fun p => ⟨(p.1.1,p.2.1,p.2.2),p.1.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl }

/-- Exact count of admissible frames for an arbitrary predicate on the left restriction. -/
theorem rootAdmissibleFrames_card (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z) (P : (LinearMap.ker z →ₗ[ZMod 2] T) → Prop)
    (hdim : 2*Module.finrank (ZMod 2) T ≤
      Module.finrank (ZMod 2) (LinearMap.ker z)) :
    Nat.card (RootAdmissibleFrames z P)=
      Nat.card {A : LinearMap.ker z →ₗ[ZMod 2] T // Function.Surjective A ∧ P A} *
        (Nat.card T)^2 * 2^(Module.finrank (ZMod 2) T)^2 *
          ∏ i : Fin (Module.finrank (ZMod 2) T),
            (2^(Module.finrank (ZMod 2) (LinearMap.ker z)-
              Module.finrank (ZMod 2) T)-2^(i:ℕ)) := by
  classical
  letI : Finite (LinearMap.ker z →ₗ[ZMod 2] T) := Finite.of_injective
    (fun f : LinearMap.ker z →ₗ[ZMod 2] T =>
      (f : LinearMap.ker z → T)) DFunLike.coe_injective
  letI : Fintype (LinearMap.ker z →ₗ[ZMod 2] T) := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite T
  let C := 2^(Module.finrank (ZMod 2) T)^2 *
    ∏ i : Fin (Module.finrank (ZMod 2) T),
      (2^(Module.finrank (ZMod 2) (LinearMap.ker z)-
        Module.finrank (ZMod 2) T)-2^(i:ℕ))
  rw [Nat.card_congr (rootAdmissibleComponentsEquiv z hz P),
    Nat.card_congr (rootComponentsReassocEquiv z P)]
  have hfiber (A : LinearMap.ker z →ₗ[ZMod 2] T)
      (_ : Function.Surjective A ∧ P A) :
      Nat.card {p : (LinearMap.ker z →ₗ[ZMod 2] T) × T × T //
        Function.Surjective (A.prod p.1)}=C*(Nat.card T)^2 := by
    rw [Nat.card_congr (rootFiberEquiv z A),Nat.card_prod,Nat.card_prod,
      jointSurjectiveLinearMaps_card A ‹Function.Surjective A ∧ P A›.1 hdim]
    simp [C,pow_two]
  have hc := card_subtype_prod_of_constant_fibers
    (A := LinearMap.ker z →ₗ[ZMod 2] T)
    (B := (LinearMap.ker z →ₗ[ZMod 2] T) × T × T)
    (fun A : LinearMap.ker z →ₗ[ZMod 2] T => Function.Surjective A ∧ P A)
    (fun A p => Function.Surjective (A.prod p.1)) (C*(Nat.card T)^2) hfiber
  rw [hc]
  dsimp [C]
  ring

end BinaryFieldCounterexamples.Trees
