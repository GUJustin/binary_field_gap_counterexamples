/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectiveLinearCount
public import BinaryFieldCounterexamples.Constructions.Trees.ConstrainedLinearPullbacks
/-!
# Actual constrained base frames

Literal coordinate maps identify constrained surjective linear maps with independent frames.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Literal coordinate frames of linear maps to the height-two template space. -/
def baseLinearFrameEquiv : (V →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃ (Fin 3 → Module.Dual (ZMod 2) V) :=
  { toFun := fun L i => (LinearMap.proj i).comp L
    invFun := LinearMap.pi
    left_inv := by intro L; rfl
    right_inv := by intro s; rfl }
/-- A literal base coordinate frame is independent exactly when its map is onto. -/
theorem baseLinearFrame_independent_iff (L : V →ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    LinearIndependent (ZMod 2) (baseLinearFrameEquiv L) ↔ Function.Surjective L := by
  let e := Pi.basisFun (ZMod 2) (Fin 3)
  have he : baseLinearFrameEquiv L = L.dualMap ∘ e.dualBasis := by
    ext i x
    simp only [Function.comp_apply,LinearMap.dualMap_apply,Module.Basis.dualBasis_apply]
    rfl
  rw [he]
  constructor
  · intro h
    exact LinearMap.dualMap_injective_iff.mp
      (LinearMap.injective_of_linearIndependent e.dualBasis.span_eq h)
  · intro h
    exact e.dualBasis.linearIndependent.map' L.dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_iff.mpr h))
/-- The actual constrained maps are exactly independent coordinate frames with the same property. -/
def baseConstrainedFrameEquiv (P : (V → ZMod 2) → Prop) :
    ConstrainedSurjectiveLinearMaps baseTemplate P ≃
      {s : Fin 3 → Module.Dual (ZMod 2) V // LinearIndependent (ZMod 2) s ∧
        P (fun x => baseTemplate (fun i => s i x))} :=
  baseLinearFrameEquiv.subtypeEquiv
    (p := fun L : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) =>
      Function.Surjective L ∧ P (fun x => baseTemplate (L x)))
    (q := fun s : Fin 3 → Module.Dual (ZMod 2) V =>
      LinearIndependent (ZMod 2) s ∧ P (fun x => baseTemplate (fun i => s i x)))
    (fun L => and_congr (baseLinearFrame_independent_iff L).symm Iff.rfl)
end BinaryFieldCounterexamples.Trees
