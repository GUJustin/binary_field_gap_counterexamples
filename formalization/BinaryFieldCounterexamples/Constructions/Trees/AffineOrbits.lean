/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Leaves
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# Actual affine families and stabilizers of tree templates

Families are literal orbits of binary functions under affine automorphisms.
The finite orbit-stabilizer identity is proved for these concrete families.
Affine changes preserve balance and the absence of translation periods;
minimal templates also have an explicit complementing translation.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Affine coordinate changes act on binary functions by inverse precomposition. -/
def affineFunctionMulAction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    MulAction (V ≃ᵃ[ZMod 2] V) (V → ZMod 2) :=
  { smul := fun e f x => f (e.symm x)
    one_smul := by intro f; rfl
    mul_smul := by intro e e' f; rfl }
attribute [local instance] affineFunctionMulAction

/-- The actual family of all affine coordinate changes of a function. -/
def affineFunctionFamily {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) : Set (V → ZMod 2) := MulAction.orbit (V ≃ᵃ[ZMod 2] V) f
/-- Literal affine stabilizers of a binary function. -/
def affineFunctionStabilizer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) : Subgroup (V ≃ᵃ[ZMod 2] V) := MulAction.stabilizer (V ≃ᵃ[ZMod 2] V) f
/-- Stabilizer membership is the usual pointwise invariance equation. -/
theorem mem_affineFunctionStabilizer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (e : V ≃ᵃ[ZMod 2] V) :
    e ∈ affineFunctionStabilizer f ↔ ∀ x, f (e x)=f x := by
  change (fun x => f (e.symm x))=f ↔ _
  constructor
  · intro h x
    simpa using (congrFun h (e x)).symm
  · intro h
    funext x
    simpa using (h (e.symm x)).symm
/-- Affine functions on a finite space have finitely many coordinate changes. -/
noncomputable def affineEquivFintype {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] :
    Fintype (V ≃ᵃ[ZMod 2] V) := by
  classical
  exact Fintype.ofInjective (fun e : V ≃ᵃ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
attribute [local instance] affineEquivFintype

/-- The literal orbit and stabilizer satisfy exact finite counting. -/
theorem affineFunctionFamily_card_mul_stabilizer {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (f : V → ZMod 2) :
    Nat.card (affineFunctionFamily f)*Nat.card (affineFunctionStabilizer f)=Nat.card (V ≃ᵃ[ZMod 2] V) := by
  classical
  rw [affineFunctionFamily,affineFunctionStabilizer]
  simpa only [Nat.card_eq_fintype_card] using MulAction.card_orbit_mul_card_stabilizer_eq_card_group (V ≃ᵃ[ZMod 2] V) f
/-- Translation periods are transported by the linear part of an affine coordinate change. -/
theorem affine_precompose_period_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (e : V ≃ᵃ[ZMod 2] V) (u : V) :
    IsPeriod (fun x => f (e x)) u ↔ IsPeriod f (e.linear u) := by
  have he (x : V) : e (x+u)=e x+e.linear u := by
    simpa [add_comm] using e.map_vadd x u
  constructor
  · intro h x
    obtain ⟨y,rfl⟩ := e.surjective x
    simpa only [he] using h y
  · intro h x
    dsimp only
    rw [he]
    exact h (e x)
/-- Literal binary fiber counts are unchanged by affine coordinates. -/
theorem affine_precompose_fiber_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (e : V ≃ᵃ[ZMod 2] V) (b : ZMod 2) :
    Nat.card {x : V // f (e x)=b}=Nat.card {x : V // f x=b} := by
  exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun _ => Iff.rfl))
/-- A fixed translation complements the minimal template. -/
def templateComplementVector : (n : ℕ) → TemplateSpace n
  | 0 => ![0,0,1]
  | n+1 => (0,templateComplementVector n,templateComplementVector n)
/-- Complementation of the template is an actual affine translation. -/
theorem template_add_complementVector (n : ℕ) (x : TemplateSpace n) :
    template n (x+templateComplementVector n)=template n x+1 := by
  induction n with
  | zero => change (x 0+0)*(x 1+0)+(x 2+1)=(x 0*x 1+x 2)+1; ring
  | succ n ih =>
    change (if x.1+0=0 then template n (x.2.1+templateComplementVector n)
      else template n (x.2.2+templateComplementVector n))=(if x.1=0 then template n x.2.1 else template n x.2.2)+1
    simp only [add_zero,ih]
    split_ifs <;> rfl
/-- An affine automorphism is uniquely its translation and linear part. -/
def affineEquivCoordinates {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ᵃ[ZMod 2] V) ≃ V × (V ≃ₗ[ZMod 2] V) :=
  { toFun := fun e => (e 0,e.linear)
    invFun := fun p => p.2.toAffineEquiv.trans (AffineEquiv.constVAdd (ZMod 2) V p.1)
    left_inv := by
      intro e
      ext x
      have h := e.map_vadd (0:V) x
      simpa [add_comm] using h.symm
    right_inv := by
      intro p
      apply Prod.ext
      · simp
      · ext x
        rfl }
/-- The affine automorphism count separates translations from linear frames. -/
theorem affineEquiv_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    Nat.card (V ≃ᵃ[ZMod 2] V)=Nat.card V*Nat.card (V ≃ₗ[ZMod 2] V) := by
  rw [Nat.card_congr affineEquivCoordinates,Nat.card_prod]
/-- The orbit count is the exact quotient by its actual affine stabilizer. -/
theorem affineFunctionFamily_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (f : V → ZMod 2) :
    Nat.card (affineFunctionFamily f)=
      Nat.card V*Nat.card (V ≃ₗ[ZMod 2] V)/Nat.card (affineFunctionStabilizer f) := by
  have hpos : 0<Nat.card (affineFunctionStabilizer f) := Nat.card_pos
  rw [←affineEquiv_card,←affineFunctionFamily_card_mul_stabilizer f,Nat.mul_div_cancel _ hpos]
/-- Every function in the actual minimal affine orbit has no nonzero translation period. -/
theorem affine_template_period_iff (n : ℕ) (e : TemplateSpace n ≃ᵃ[ZMod 2] TemplateSpace n) (u : TemplateSpace n) :
    IsPeriod (fun x => template n (e x)) u ↔ u=0 := by
  rw [affine_precompose_period_iff,template_period_iff]
  exact e.linear.map_eq_zero_iff
/-- Every function in the actual minimal affine orbit is balanced. -/
theorem affine_template_fiber_card (n : ℕ) (e : TemplateSpace n ≃ᵃ[ZMod 2] TemplateSpace n) (b : ZMod 2) :
    Nat.card {x : TemplateSpace n // template n (e x)=b}=2^(2^(n+2)-2) := by
  rw [affine_precompose_fiber_card,template_fiber_card]
end BinaryFieldCounterexamples.Trees

