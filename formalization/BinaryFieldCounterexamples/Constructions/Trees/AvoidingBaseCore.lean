/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.BaseCount
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
/-!
# Origin stabilizers of the base template

Kernel-checked finite enumeration gives the six origin-fixing stabilizers
and transitivity on the four zeros. These identify the exact denominator
for constrained linear height-two pullbacks.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] binaryFintype
attribute [local instance] baseAffineDataFintype
/-- Exactly six affine stabilizers of the base template fix the origin. -/
theorem baseTemplate_origin_stabilizer_card :
    Nat.card {e : affineFunctionStabilizer baseTemplate // e.1 0=0}=6 := by
  let e := baseStabilizerDataEquiv.subtypeEquiv (p := fun e => e.1 0=0) (q := fun p => p.1.1=0)
    (show ∀ p : affineFunctionStabilizer baseTemplate, p.1 0=0 ↔ (baseStabilizerDataEquiv p).1.1=0 from fun _ => Iff.rfl)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  decide +kernel
/-- Each zero of the base template is an attainable stabilizer translation. -/
theorem baseAffineData_exists_zero_image (c : (Fin 3 → ZMod 2)) (hc : baseTemplate c=0) :
    ∃ p : baseAffineData, p.1.1=c := by
  have h : ∀ c : (Fin 3 → ZMod 2), baseTemplate c=0 → ∃ p : baseAffineData, p.1.1=c := by decide +kernel
  exact h c hc
/-- The actual affine stabilizer is transitive on the zeros of the base template. -/
theorem baseTemplate_stabilizer_zero_image (c : (Fin 3 → ZMod 2)) (hc : baseTemplate c=0) :
    ∃ e : affineFunctionStabilizer baseTemplate, e.1 0=c := by
  obtain ⟨p,hp⟩ := baseAffineData_exists_zero_image c hc
  refine ⟨baseStabilizerDataEquiv.symm p,?_⟩
  have he := congrArg (fun p : baseAffineData => p.1.1) (baseStabilizerDataEquiv.apply_symm_apply p)
  exact he.trans hp
end BinaryFieldCounterexamples.Trees
