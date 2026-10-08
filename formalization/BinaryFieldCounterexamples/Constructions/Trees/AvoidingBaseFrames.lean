/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingBaseRestriction
public import BinaryFieldCounterexamples.Constructions.Trees.ConstrainedFrames
/-!
# Actual constrained base frames

The annihilator restriction bridge gives the exact population of actual independent base frames vanishing on a prescribed codimension-three subspace.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Annihilator membership is zero restriction. -/
theorem annihilator_mem_restrict_zero (W : Submodule (ZMod 2) V) (a : Module.Dual (ZMod 2) V) :
    a ∈ W.dualAnnihilator ↔ a.comp W.subtype=0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h; ext x; exact h x.1 x.2
  · intro h x hx
    exact congrArg (fun f : Module.Dual (ZMod 2) W => f ⟨x,hx⟩) h
/-- Binary sums lie in the annihilator exactly when their restrictions agree. -/
theorem annihilator_add_mem_iff (W : Submodule (ZMod 2) V) (a b : Module.Dual (ZMod 2) V) :
    a+b ∈ W.dualAnnihilator ↔ a.comp W.subtype=b.comp W.subtype := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h; ext x; exact CharTwo.add_eq_zero.mp (h x.1 x.2)
  · intro h x hx
    exact CharTwo.add_eq_zero.mpr (congrArg (fun f : Module.Dual (ZMod 2) W => f ⟨x,hx⟩) h)
/-- The frame condition is precisely the actual base function vanishing on the prescribed subspace. -/
theorem constrainedFrameCondition_iff_vanish (W : Submodule (ZMod 2) V)
    (s : Fin 3 → Module.Dual (ZMod 2) V) :
    ((s 0 ∈ W.dualAnnihilator ∧ s 2 ∈ W.dualAnnihilator) ∨
      (s 1 ∈ W.dualAnnihilator ∧ s 2 ∈ W.dualAnnihilator) ∨
      (s 0+s 1 ∈ W.dualAnnihilator ∧ s 0+s 2 ∈ W.dualAnnihilator)) ↔
    ∀ x : W, baseTemplate (fun i => s i x)=0 := by
  rw [annihilator_add_mem_iff,annihilator_add_mem_iff]
  simp only [annihilator_mem_restrict_zero]
  rw [show (∀ x : W, baseTemplate (fun i => s i x)=0) =
      (∀ x : W, (s 0).comp W.subtype x*(s 1).comp W.subtype x+(s 2).comp W.subtype x=0) from rfl]
  rw [quadratic_zero_restriction_iff]
  tauto
/-- The actual vanishing independent base frames have the exact constrained population. -/
theorem vanishingBaseFrames_card [Fintype V] (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+3=Module.finrank (ZMod 2) V) :
    Nat.card {s : Fin 3 → Module.Dual (ZMod 2) V //
      LinearIndependent (ZMod 2) s ∧ ∀ x : W, baseTemplate (fun i => s i x)=0} =
      168+126*(2^Module.finrank (ZMod 2) V-8) := by
  classical
  let : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofInjective
    (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective
  have hd : Module.finrank (ZMod 2) W.dualAnnihilator=3 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  let e := (Equiv.refl (Fin 3 → Module.Dual (ZMod 2) V)).subtypeEquiv
    (p := fun s => LinearIndependent (ZMod 2) s ∧
      ((s 0 ∈ W.dualAnnihilator ∧ s 2 ∈ W.dualAnnihilator) ∨
      (s 1 ∈ W.dualAnnihilator ∧ s 2 ∈ W.dualAnnihilator) ∨
      (s 0+s 1 ∈ W.dualAnnihilator ∧ s 0+s 2 ∈ W.dualAnnihilator)))
    (q := fun s : Fin 3 → Module.Dual (ZMod 2) V => LinearIndependent (ZMod 2) s ∧ ∀ x : W, baseTemplate (fun i => s i x)=0)
    (fun s => and_congr Iff.rfl (constrainedFrameCondition_iff_vanish W s))
  rw [←Nat.card_congr e]
  exact (constrainedFrames_card W.dualAnnihilator hd).trans (by rw [Subspace.dual_finrank_eq])
end BinaryFieldCounterexamples.Trees
