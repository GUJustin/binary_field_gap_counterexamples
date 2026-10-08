/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingFamily
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Actual admissible tree roots

Constrained surjective frames determine nonzero annihilator functionals.
Their exact population and actual kernel dimensions supply the root factor
and recursive prescribed subspace for the avoiding-family count.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Actual nonzero root functionals annihilating the prescribed subspace. -/
def AvoidingRoots (W : Submodule (ZMod 2) V) := {z : W.dualAnnihilator // z≠0}
/-- The actual root functional of a constrained surjective parent frame. -/
def avoidingFrameRoot (n : ℕ) (W : Submodule (ZMod 2) V)
    (L : {L : V →ₗ[ZMod 2] TemplateSpace (n+1) // Function.Surjective L ∧
      avoidingTreeFrameProperty (n+1) W L}) : AvoidingRoots W := by
  let z : Module.Dual (ZMod 2) V := (LinearMap.fst (ZMod 2) (ZMod 2)
    (TemplateSpace n × TemplateSpace n)).comp L.1
  have hzW : z ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact (L.2.2 ⟨x,hx⟩).1
  refine ⟨⟨z,hzW⟩,?_⟩
  intro hz
  obtain ⟨x,hx⟩ := L.2.1 (1,0,0)
  have hzx : z x=0 := congrArg (fun z : W.dualAnnihilator => z.1 x) hz
  have hzx1 : z x=1 := by change (L.1 x).1=1; rw [hx]
  exact zero_ne_one (hzx.symm.trans hzx1)
/-- The finite root population is exactly the nonzero annihilator population. -/
theorem avoidingRoots_card [Fintype V] (W : Submodule (ZMod 2) V) :
    Nat.card (AvoidingRoots W)=2^(Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W)-1 := by
  classical
  let : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofInjective
    (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective
  let : Fintype W.dualAnnihilator := Fintype.ofFinite _
  have hd : Module.finrank (ZMod 2) W.dualAnnihilator=
      Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  change Nat.card {z : W.dualAnnihilator // z≠0}=_
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
    Module.card_eq_pow_finrank (K := ZMod 2),hd]
  norm_num
/-- A nonzero binary functional is onto the binary field. -/
theorem binaryFunctional_surjective (z : Module.Dual (ZMod 2) V) (hz : z≠0) : Function.Surjective z := by
  obtain ⟨x,hx⟩ : ∃ x, z x≠0 := by
    by_contra h
    apply hz
    ext x
    simpa using not_exists.mp h x
  have hx1 : z x=1 := by
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (z x) with h|h
    · exact False.elim (hx h)
    · exact h
  intro b
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) b with rfl|rfl
  · exact ⟨0,map_zero z⟩
  · exact ⟨x,hx1⟩
/-- An actual root kernel has codimension one. -/
theorem binaryFunctional_ker_finrank [Finite V] (z : Module.Dual (ZMod 2) V) (hz : z≠0) :
    Module.finrank (ZMod 2) (LinearMap.ker z)+1=Module.finrank (ZMod 2) V := by
  have h := z.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (binaryFunctional_surjective z hz),finrank_top,
    Module.finrank_self] at h
  omega
/-- The prescribed subspace lies in every admissible actual root kernel. -/
theorem avoidingRoot_le_ker (W : Submodule (ZMod 2) V) (z : AvoidingRoots W) :
    W ≤ LinearMap.ker z.1.1 := by
  intro x hx
  exact (Submodule.mem_dualAnnihilator z.1.1).mp z.1.2 x hx
/-- The prescribed subspace as an actual subspace of an admissible root kernel. -/
def avoidingRootSubspace (W : Submodule (ZMod 2) V) (z : AvoidingRoots W) :
    Submodule (ZMod 2) (LinearMap.ker z.1.1) := W.comap (LinearMap.ker z.1.1).subtype
/-- Passing into an actual root kernel preserves the prescribed subspace dimension. -/
theorem avoidingRootSubspace_finrank [Finite V] (W : Submodule (ZMod 2) V) (z : AvoidingRoots W) :
    Module.finrank (ZMod 2) (avoidingRootSubspace W z)=Module.finrank (ZMod 2) W := by
  exact (Submodule.comapSubtypeEquivOfLe (avoidingRoot_le_ker W z)).finrank_eq
/-- Every admissible root is nonzero as an actual functional. -/
theorem avoidingRoot_ne_zero (W : Submodule (ZMod 2) V) (z : AvoidingRoots W) : z.1.1≠0 := by
  intro h
  exact z.2 (Subtype.ext h)
end BinaryFieldCounterexamples.Trees
