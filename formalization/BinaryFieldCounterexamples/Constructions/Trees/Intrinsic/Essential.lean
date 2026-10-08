/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.BranchRecovery
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Essential coordinates of Boolean functions

This module formalizes the essential dual space and essential dimension in the
paper's Definition `def:tree-periods` (translation periods and essential
coordinates). The essential dual space is literally the annihilator of the
existing translation-period submodule. No polynomial degree is used here.
Surjective affine pullback transports this space by the dual linear map; in
particular a period-free function pulled back from a minimal space has that
space's dimension as its essential dimension.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open Module
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The linear functionals that vanish on every translation period of `f`. -/
def essentialDualSpace (f : V → ZMod 2) : Submodule (ZMod 2) (Dual (ZMod 2) V) :=
  (periodSubmodule f).dualAnnihilator

/-- The dimension of the essential dual space, as in Definition `def:tree-periods`. -/
noncomputable def essentialDimension (f : V → ZMod 2) : ℕ :=
  finrank (ZMod 2) (essentialDualSpace f)

/-- Membership spells out the paper's vanishing-on-periods condition. -/
theorem mem_essentialDualSpace (f : V → ZMod 2) (ℓ : Dual (ZMod 2) V) :
    ℓ ∈ essentialDualSpace f ↔ ∀ u, IsPeriod f u → ℓ u = 0 := by
  exact Submodule.mem_dualAnnihilator _

/-- The ignored and essential dimensions sum to the dimension of the domain. -/
theorem essentialDimension_add_finrank_periodSubmodule [FiniteDimensional (ZMod 2) V]
    (f : V → ZMod 2) :
    essentialDimension f + finrank (ZMod 2) (periodSubmodule f) = finrank (ZMod 2) V := by
  change finrank (ZMod 2) (periodSubmodule f).dualAnnihilator +
    finrank (ZMod 2) (periodSubmodule f) = finrank (ZMod 2) V
  exact (Nat.add_comm _ _).trans
    (Subspace.finrank_add_finrank_dualAnnihilator_eq (periodSubmodule f))

/-- Essential dimension is the codimension of the translation-period space. -/
theorem essentialDimension_eq_finrank_sub [FiniteDimensional (ZMod 2) V]
    (f : V → ZMod 2) :
    essentialDimension f = finrank (ZMod 2) V - finrank (ZMod 2) (periodSubmodule f) := by
  have := essentialDimension_add_finrank_periodSubmodule f
  omega

/-- The quotient by ignored directions has exactly the essential dimension. -/
theorem essentialDimension_eq_finrank_quotient_periodSubmodule
    [FiniteDimensional (ZMod 2) V] (f : V → ZMod 2) :
    essentialDimension f = finrank (ZMod 2) (V ⧸ periodSubmodule f) := by
  change finrank (ZMod 2) (periodSubmodule f).dualAnnihilator = _
  exact (Subspace.quotEquivAnnihilator (periodSubmodule f)).finrank_eq.symm

/-- Essential dimension cannot exceed the number of domain coordinates. -/
theorem essentialDimension_le_finrank [FiniteDimensional (ZMod 2) V]
    (f : V → ZMod 2) : essentialDimension f ≤ finrank (ZMod 2) V := by
  have := essentialDimension_add_finrank_periodSubmodule f
  omega

/-- Equality of essential coordinate spaces is equivalent to equality of ignored directions. -/
theorem essentialDualSpace_eq_iff_periodSubmodule_eq (f g : V → ZMod 2) :
    essentialDualSpace f = essentialDualSpace g ↔ periodSubmodule f = periodSubmodule g := by
  exact Subspace.dualAnnihilator_inj

/-- Essential coordinates recover precisely the directions ignored by the function. -/
theorem essentialDualSpace_dualCoannihilator (f : V → ZMod 2) :
    (essentialDualSpace f).dualCoannihilator = periodSubmodule f := by
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

/-- Complementation changes no translation periods. -/
@[simp] theorem periodSubmodule_complement (f : V → ZMod 2) :
    periodSubmodule (fun x => f x + 1) = periodSubmodule f := by
  ext u
  change (∀ x, f (x + u) + 1 = f x + 1) ↔ ∀ x, f (x + u) = f x
  simp only [add_left_inj]

/-- Complementation changes no essential coordinates. -/
@[simp] theorem essentialDualSpace_complement (f : V → ZMod 2) :
    essentialDualSpace (fun x => f x + 1) = essentialDualSpace f := by
  simp [essentialDualSpace]

/-- Complementation preserves essential dimension. -/
@[simp] theorem essentialDimension_complement (f : V → ZMod 2) :
    essentialDimension (fun x => f x + 1) = essentialDimension f := by
  unfold essentialDimension
  rw [essentialDualSpace_complement]

/-- Surjective affine pullback takes the inverse image of the period space. -/
theorem periodSubmodule_affineMap_precompose (f : W → ZMod 2)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    periodSubmodule (fun x => f (a x)) = (periodSubmodule f).comap a.linear := by
  ext u
  exact affineMap_precompose_period_iff f a ha u

/-- For a surjective linear map, annihilation of an inverse image is dual pullback. -/
theorem dualAnnihilator_comap_of_surjective (P : Submodule (ZMod 2) W)
    (L : V →ₗ[ZMod 2] W) (hL : Function.Surjective L) :
    (P.comap L).dualAnnihilator = P.dualAnnihilator.map L.dualMap := by
  apply le_antisymm
  · intro ℓ hℓ
    have hker : ℓ ∈ L.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator] at hℓ ⊢
      intro u hu
      apply hℓ u
      change L u ∈ P
      simpa only [LinearMap.mem_ker.mp hu] using P.zero_mem
    rw [← L.range_dualMap_eq_dualAnnihilator_ker] at hker
    obtain ⟨m, hm⟩ := hker
    refine ⟨m, ?_, hm⟩
    apply (Submodule.mem_dualAnnihilator m).mpr
    intro w hw
    obtain ⟨u, rfl⟩ := hL w
    rw [← LinearMap.dualMap_apply, hm]
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ u hw
  · exact Submodule.dualAnnihilator_map_dualMap_le P L

/-- Essential coordinates under a surjective affine pullback are pulled-back functionals. -/
theorem essentialDualSpace_affineMap_precompose (f : W → ZMod 2)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    essentialDualSpace (fun x => f (a x)) = (essentialDualSpace f).map a.linear.dualMap := by
  rw [essentialDualSpace, periodSubmodule_affineMap_precompose f a ha]
  exact dualAnnihilator_comap_of_surjective _ _ (a.linear_surjective_iff.mpr ha)

/-- Surjective affine pullback preserves essential dimension. -/
theorem essentialDimension_affineMap_precompose (f : W → ZMod 2)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    essentialDimension (fun x => f (a x)) = essentialDimension f := by
  rw [essentialDimension, essentialDualSpace_affineMap_precompose f a ha]
  exact (Submodule.equivMapOfInjective _
    (LinearMap.dualMap_injective_of_surjective (a.linear_surjective_iff.mpr ha)) _).finrank_eq.symm

/-- Invertible affine changes preserve essential dimension (Lemma `lem:tree-structure`, part 2). -/
theorem essentialDimension_affineEquiv_precompose (f : W → ZMod 2)
    (e : V ≃ᵃ[ZMod 2] W) :
    essentialDimension (fun x => f (e x)) = essentialDimension f := by
  exact essentialDimension_affineMap_precompose f e.toAffineMap e.surjective

/-- Invertible affine coordinates pull essential functionals back by their linear part. -/
theorem essentialDualSpace_affineEquiv_precompose (f : W → ZMod 2)
    (e : V ≃ᵃ[ZMod 2] W) :
    essentialDualSpace (fun x => f (e x)) =
      (essentialDualSpace f).map e.linear.toLinearMap.dualMap := by
  exact essentialDualSpace_affineMap_precompose f e.toAffineMap e.surjective

/-- The linear pullback specialization has the same intrinsic essential dimension. -/
theorem essentialDimension_linearMap_precompose (f : W → ZMod 2)
    (L : V →ₗ[ZMod 2] W) (hL : Function.Surjective L) :
    essentialDimension (fun x => f (L x)) = essentialDimension f := by
  exact essentialDimension_affineMap_precompose f L.toAffineMap hL

/-- For a period-free function the pullback's periods are exactly the map's kernel. -/
theorem periodSubmodule_affineMap_precompose_periodFree (f : W → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u = 0)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    periodSubmodule (fun x => f (a x)) = a.linear.ker := by
  ext u
  exact (affineMap_precompose_period_iff f a ha u).trans (hf _)

/-- A period-free pullback has the annihilator of its quotient kernel as essential space. -/
theorem essentialDualSpace_affineMap_precompose_periodFree (f : W → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u = 0)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    essentialDualSpace (fun x => f (a x)) = a.linear.ker.dualAnnihilator := by
  rw [essentialDualSpace, periodSubmodule_affineMap_precompose_periodFree f hf a ha]

/-- Every coordinate is essential for a period-free function. -/
theorem essentialDualSpace_eq_top_of_periodFree (f : V → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u = 0) : essentialDualSpace f = ⊤ := by
  have hp : periodSubmodule f = ⊥ := by ext u; exact hf u
  simp [essentialDualSpace, hp]

/-- A period-free function has the entire domain as its essential dimension. -/
theorem essentialDimension_eq_finrank_of_periodFree (f : V → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u = 0) : essentialDimension f = finrank (ZMod 2) V := by
  rw [essentialDimension, essentialDualSpace_eq_top_of_periodFree f hf]
  simp [Subspace.dual_finrank_eq]

/-- A surjective affine pullback of a period-free function has its minimal-space dimension. -/
theorem essentialDimension_affineMap_precompose_periodFree (f : W → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u = 0)
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    essentialDimension (fun x => f (a x)) = finrank (ZMod 2) W := by
  rw [essentialDimension_affineMap_precompose f a ha,
    essentialDimension_eq_finrank_of_periodFree f hf]
end BinaryFieldCounterexamples.Trees
