/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AffineOrbits
/-!
# Origin-fixing stabilizer factors

Actual point-orbit transitivity gives the exact zero-fiber factor in the
affine stabilizer population.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
/-- Affine automorphisms act on actual points. -/
def affinePointMulAction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    MulAction (V ≃ᵃ[ZMod 2] V) V :=
  { smul := fun e x => e x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
attribute [local instance] affinePointMulAction
/-- Transitivity on the actual zero fiber gives the exact origin-stabilizer factor. -/
theorem zeroFiber_card_mul_origin_stabilizer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (hzero : f 0=0)
    (htrans : ∀ c, f c=0 → ∃ e : affineFunctionStabilizer f, e.1 0=c) :
    Nat.card {x : V // f x=0} * Nat.card {e : affineFunctionStabilizer f // e.1 0=0} =
      Nat.card (affineFunctionStabilizer f) := by
  have he : MulAction.orbit (affineFunctionStabilizer f) (0:V)={x | f x=0} := by
    ext x
    constructor
    · rintro ⟨e,rfl⟩
      change f (e.1 0)=0
      rw [(mem_affineFunctionStabilizer f e.1).mp e.2,hzero]
    · intro hx
      obtain ⟨e,he⟩ := htrans x hx
      exact ⟨e,he⟩
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (affineFunctionStabilizer f) (0:V))
  rw [Nat.card_prod] at h
  have hc : Nat.card (MulAction.orbit (affineFunctionStabilizer f) (0:V))=
      Nat.card {x : V // f x=0} := Nat.card_congr (Equiv.cast (congrArg (fun S : Set V => ↥S) he))
  rw [hc] at h
  exact h
end BinaryFieldCounterexamples.Trees
