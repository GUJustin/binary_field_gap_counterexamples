/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Templates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.ZMod.Basic

/-!
# Surjective binary linear-map populations

Coordinate dual frames turn surjectivity into linear independence. Their exact
finite product count supplies the prescribed-domain tree family population.
-/

@[expose] public section
set_option maxHeartbeats 1000000
namespace BinaryFieldCounterexamples.Trees

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Coordinates identify linear maps with frames in the domain dual. -/
noncomputable def linearMapDualFrameEquiv (e : Module.Basis (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W) :
    (V →ₗ[ZMod 2] W) ≃ (Fin (Module.finrank (ZMod 2) W) → Module.Dual (ZMod 2) V) := {
  toFun L i := (e.coord i).comp L
  invFun s := e.equivFun.symm.toLinearMap.comp (LinearMap.pi s)
  left_inv L := by
    ext x
    apply e.equivFun.injective
    simp
  right_inv s := by
    funext i
    ext x
    change e.equivFun (e.equivFun.symm (fun j => s j x)) i = s i x
    exact congrArg (fun f => f i) (e.equivFun.apply_symm_apply (fun j => s j x))

  }

/-- A coordinate dual frame is independent exactly when the map is onto. -/
theorem linearMapDualFrame_independent_iff
    (e : Module.Basis (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W) (L : V →ₗ[ZMod 2] W) :
    LinearIndependent (ZMod 2) (linearMapDualFrameEquiv e L) ↔ Function.Surjective L := by
  change LinearIndependent (ZMod 2) (L.dualMap ∘ e.coord) ↔ _
  rw [← e.coe_dualBasis]
  constructor
  · intro h
    exact LinearMap.dualMap_injective_iff.mp
      (LinearMap.injective_of_linearIndependent e.dualBasis.span_eq h)
  · intro h
    exact e.dualBasis.linearIndependent.map' L.dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_iff.mpr h))

variable [Finite V] [Finite W]

/-- Exact count of surjective binary linear maps. -/
theorem surjectiveLinearMaps_card (hdim : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V) :
    Nat.card {L : V →ₗ[ZMod 2] W // Function.Surjective L} =
      ∏ i : Fin (Module.finrank (ZMod 2) W),
        (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
  classical
  let : Finite (Module.Dual (ZMod 2) V) := Finite.of_injective
    (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective
  let e := Module.finBasis (ZMod 2) W
  let E := (linearMapDualFrameEquiv (V := V) e).subtypeEquiv
    (p := fun L : V →ₗ[ZMod 2] W => Function.Surjective L)
    (q := fun s => LinearIndependent (ZMod 2) s)
    (fun L => (linearMapDualFrame_independent_iff e L).symm)
  rw [Nat.card_congr E]
  rw [card_linearIndependent]
  · simp [Subspace.dual_finrank_eq]
  · simpa [Subspace.dual_finrank_eq] using hdim

end BinaryFieldCounterexamples.Trees
