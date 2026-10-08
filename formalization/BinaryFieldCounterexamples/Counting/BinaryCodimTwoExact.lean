/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
import Mathlib.Tactic.NormNum
/-!
# Exact codimension-two binary subspace population

The existing family of common kernels is precisely the family of subgroups
of quarter cardinality. Its exact count follows from the actual Gaussian
subspace count and the injective dual-coannihilator correspondence.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- The existing pair-span family contains exactly the binary rank-two subspaces. -/
theorem mem_binaryPairSpans_iff
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (W : Submodule (ZMod 2) V) :
    W ∈ binaryPairSpans ↔ Module.finrank (ZMod 2) W = 2 := by
  classical
  constructor
  · intro h
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp h
    exact finrank_binaryPairSpan s
  · intro h
    let b := (Module.finBasis (ZMod 2) W).reindex (finCongr h)
    obtain ⟨v, hv⟩ := (independentFramesEquivSubspaceBasis (k := ZMod 2) (V := V) 2).surjective
      ⟨⟨W, h⟩, b⟩
    have hs : binaryPairSpan v = W := by
      exact congrArg (fun t ↦ t.1.val) hv
    apply Finset.mem_image.mpr
    exact ⟨v, by simp [binaryIndependentPairs], hs⟩

/-- The literal pair-span family has the base-two Gaussian cardinality. -/
theorem card_binaryPairSpans_exact
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hdim : 2 ≤ Module.finrank (ZMod 2) V) :
    (binaryPairSpans (V := V)).card =
      (2 ^ Module.finrank (ZMod 2) V - 1) *
        (2 ^ Module.finrank (ZMod 2) V - 2) / 6 := by
  classical
  let e : {W // W ∈ binaryPairSpans (V := V)} ≃ subspacesOfFinrank (ZMod 2) V 2 :=
    Equiv.subtypeEquivRight (fun W ↦ mem_binaryPairSpans_iff W)
  have hc := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  rw [hc, subspacesOfFinrank_card_eq_gaussianBinomial 2 hdim]
  simp [gaussianBinomial, hdim, Finset.prod_range_succ]

/-- The actual common-kernel family has exactly (N−1)(N−2)/6 members. -/
theorem codimTwoBinarySubspaces_count_exact
    {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (D : AddSubgroup B) (hdim : 2 ≤ Module.finrank (ZMod 2) D) :
    (codimTwoBinarySubspaces D).card = (Nat.card D - 1) * (Nat.card D - 2) / 6 := by
  classical
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  have h := card_binaryPairSpans_exact (V := Module.Dual (ZMod 2) D)
    (by simpa [Subspace.dual_finrank_eq] using hdim)
  have hcard : 2 ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) D) = Nat.card D := by
    rw [Subspace.dual_finrank_eq, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]
    congr 1
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [hcard] at h
  simpa [codimTwoBinarySubspaces,
    Finset.card_image_of_injective _ (ambient_dualCoannihilator_injective D)] using h

/-- Every subgroup of quarter cardinality occurs in the existing common-kernel family. -/
theorem mem_codimTwoBinarySubspaces_of_card
    {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (D W : AddSubgroup B) (hdim : 2 ≤ Module.finrank (ZMod 2) D)
    (hle : W ≤ D) (hcard : Nat.card W = Nat.card D / 4) :
    W ∈ codimTwoBinarySubspaces D := by
  classical
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  let U : Submodule (ZMod 2) D := AddSubgroup.toZModSubmodule 2 (W.comap D.subtype)
  have hambient : ambientBinarySubspace D U = W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  have hUcard : Nat.card U = Nat.card D / 4 := by
    rw [← natCard_ambientBinarySubspace D U, hambient, hcard]
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D), htwo] at hUcard
  have hpow : 2 ^ Module.finrank (ZMod 2) D =
      2 ^ (Module.finrank (ZMod 2) D - 2) * 4 := by
    conv_lhs => rw [← Nat.sub_add_cancel hdim]
    rw [pow_add]
    norm_num
  rw [hpow, Nat.mul_div_cancel _ (by decide : 0 < 4)] at hUcard
  have hrank : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) D - 2 :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)) hUcard
  have hann : Module.finrank (ZMod 2) U.dualAnnihilator = 2 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    omega
  rw [codimTwoBinarySubspaces, Finset.mem_image]
  refine ⟨U.dualAnnihilator, (mem_binaryPairSpans_iff _).mpr hann, ?_⟩
  rw [Subspace.dualAnnihilator_dualCoannihilator_eq]
  exact hambient

/-- On a size-16K domain, exact counting and membership describe the same family. -/
theorem codimTwoBinarySubspaces_exact_of_card_sixteen_mul
    {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (D : AddSubgroup B) (K : ℕ) (hK : 0 < K) (hD : Nat.card D = 16*K) :
    (codimTwoBinarySubspaces D).card = (16*K-1)*(16*K-2)/6 ∧
      ∀ W : AddSubgroup B, W ∈ codimTwoBinarySubspaces D ↔
        W ≤ D ∧ Nat.card W = 4*K := by
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
  rw [htwo] at hc
  have hdim : 2 ≤ Module.finrank (ZMod 2) D := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hc, hD]
    norm_num
    omega
  constructor
  · simpa [hD] using codimTwoBinarySubspaces_count_exact D hdim
  · intro W
    constructor
    · intro hW
      refine ⟨codimTwoBinarySubspaces_le D W hW, ?_⟩
      have h := natCard_codimTwoBinarySubspace D W hW
      rw [hD] at h
      omega
    · rintro ⟨hle, hcard⟩
      apply mem_codimTwoBinarySubspaces_of_card D W hdim hle
      rw [hcard, hD]
      omega
end BinaryFieldCounterexamples
