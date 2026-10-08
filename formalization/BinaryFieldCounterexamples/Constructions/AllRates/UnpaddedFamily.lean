/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount

/-!
# The full finite codimension-s population

Dual coannihilators transport every s-dimensional binary dual subspace into
the supplied additive domain. Unlike the graph family used by the asymptotic
padding theorem, this family keeps the exact Gaussian count.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.AllRatesConstruction
open Finset

/-- Every supplied binary domain of dimension `m+s` contains an explicitly
counted family of `gaussianBinomial 2 (m+s) s` distinct size-`2^m` subgroups. -/
theorem exists_binary_full_subgroup_family
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (m s : ℕ) (hD : Nat.card D = 2 ^ (m+s)) :
    ∃ I : Finset (AddSubgroup B), I.card = gaussianBinomial 2 (m+s) s ∧
      ∀ W ∈ I, W ≤ D ∧ Nat.card W = 2 ^ m := by
  classical
  have hdim : Module.finrank (ZMod 2) D = m+s := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD] at h
    simp only [Nat.card_eq_fintype_card, ZMod.card] at h
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h.symm
  let V := Module.Dual (ZMod 2) D
  let _ : Finite V := Finite.of_injective (fun f : V ↦ (f : D → ZMod 2))
    LinearMap.coe_injective
  let _ : Fintype (subspacesOfFinrank (ZMod 2) V s) := Fintype.ofFinite _
  let e : subspacesOfFinrank (ZMod 2) V s → AddSubgroup B :=
    fun U ↦ ambientBinarySubspace D U.val.dualCoannihilator
  have hinj : Function.Injective e := by
    intro U W h
    exact Subtype.ext (ambient_dualCoannihilator_injective D h)
  refine ⟨Finset.univ.image e, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, subspacesOfFinrank_card_eq_gaussianBinomial]
    · simp [V, Subspace.dual_finrank_eq, hdim]
    · simp [V, Subspace.dual_finrank_eq, hdim]
  · intro W hW
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hW
    refine ⟨ambientBinarySubspace_le D _, ?_⟩
    change Nat.card (ambientBinarySubspace D U.val.dualCoannihilator) = _
    rw [natCard_ambientBinarySubspace, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    have hrank := Subspace.finrank_add_finrank_dualCoannihilator_eq U.val
    have hU : Module.finrank (ZMod 2) U.val = s := U.property
    have hco : Module.finrank (ZMod 2) U.val.dualCoannihilator = m := by
      rw [hU, hdim] at hrank
      omega
    simp [hco, Nat.card_eq_fintype_card]

end BinaryFieldCounterexamples.AllRatesConstruction
