/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import BinaryFieldCounterexamples.CollisionCounting

/-!
# Finite binary subspaces

This file supplies finite binary-subspace choices and counts in the concrete
`AddSubgroup` representation used by the paper's locator polynomials.  Internally
we use submodules over `ZMod 2`; `ambientBinarySubspace` maps them back into the
prescribed ambient additive subgroup.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- A binary subspace of the subtype `D`, viewed as an additive subgroup of the
ambient additive group. -/
def ambientBinarySubspace {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]
    (D : AddSubgroup B) (W : Submodule (ZMod 2) D) : AddSubgroup B :=
  W.toAddSubgroup.map D.subtype

/-- An ambient binary subspace lies in its prescribed domain. -/
theorem ambientBinarySubspace_le {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]
    (D : AddSubgroup B) (W : Submodule (ZMod 2) D) :
    ambientBinarySubspace D W ≤ D := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Mapping a binary subspace through the domain subtype preserves its cardinality. -/
theorem natCard_ambientBinarySubspace {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]
    (D : AddSubgroup B) (W : Submodule (ZMod 2) D) :
    Nat.card (ambientBinarySubspace D W) = Nat.card W := by
  exact AddSubgroup.card_map_of_injective D.subtype_injective

/-- Distinct binary subspaces of the domain remain distinct as ambient additive
subgroups. -/
theorem ambientBinarySubspace_injective {B : Type*} [AddCommGroup B]
    [Module (ZMod 2) B] (D : AddSubgroup B) :
    Function.Injective (ambientBinarySubspace D) := by
  intro U W h
  apply Submodule.toAddSubgroup_injective
  exact AddSubgroup.map_injective D.subtype_injective h

/-- Every power-of-two size no larger than a finite binary additive domain is
realized by an additive subgroup of that domain. -/
theorem exists_binary_subspace_card_eq
    {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    (D : AddSubgroup B) (M : ℕ) (hpow : ∃ m : ℕ, M = 2 ^ m)
    (hle : M ≤ Nat.card D) :
    ∃ U : AddSubgroup B, U ≤ D ∧ Nat.card U = M := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := hpow
  let H : Submodule (ZMod 2) B := AddSubgroup.toZModSubmodule 2 D
  have hleH : 2 ^ m ≤ Nat.card H := by
    simpa [H] using hle
  obtain ⟨W, hWle, hWlt, hWD⟩ :=
    ZModModule.exists_submodule_subset_card_le (p := 2) Nat.prime_two H hleH
      (pow_ne_zero _ (by omega))
  have hWpow : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
      show Nat.card (ZMod 2) = 2 by
        rw [Nat.card_eq_fintype_card]
        exact ZMod.card 2]
  have hrle : Module.finrank (ZMod 2) W ≤ m := by
    rw [hWpow, Nat.pow_le_pow_iff_right (by omega : 1 < 2)] at hWle
    exact hWle
  have hcard : Nat.card W = 2 ^ m := by
    rw [hWpow]
    apply congrArg (2 ^ ·)
    apply le_antisymm hrle
    by_contra! hmlt
    have hsucc : Module.finrank (ZMod 2) W + 1 ≤ m := by omega
    have hpowsucc : 2 ^ (Module.finrank (ZMod 2) W + 1) ≤ 2 ^ m :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mpr hsucc
    rw [pow_succ, ← hWpow] at hpowsucc
    omega
  refine ⟨W.toAddSubgroup, ?_, ?_⟩
  · intro x hx
    have hxH : x ∈ H := hWD hx
    simpa [H] using hxH
  · exact hcard

section IndependentPairs

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Ordered independent pairs in a finite binary vector space. -/
noncomputable def binaryIndependentPairs [Finite V] :
    Finset {s : Fin 2 → V // LinearIndependent (ZMod 2) s} := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype V := Fintype.ofFinite V
  exact Finset.univ

/-- The subspace spanned by an ordered independent pair. -/
def binaryPairSpan (s : {s : Fin 2 → V // LinearIndependent (ZMod 2) s}) :
    Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range (s : Fin 2 → V))

/-- Independent ordered binary pairs are counted by `(2^d-1)(2^d-2)` in
dimension `d`. -/
theorem card_binaryIndependentPairs [Finite V]
    (hdim : 2 ≤ Module.finrank (ZMod 2) V) :
    (binaryIndependentPairs (V := V)).card =
      (2 ^ Module.finrank (ZMod 2) V - 1) *
        (2 ^ Module.finrank (ZMod 2) V - 2) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype V := Fintype.ofFinite V
  rw [binaryIndependentPairs, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_linearIndependent hdim]
  simp [Fin.prod_univ_two]

/-- The finite family of two-dimensional subspaces spanned by independent
ordered pairs. -/
noncomputable def binaryPairSpans [Finite V] : Finset (Submodule (ZMod 2) V) := by
  classical
  exact (binaryIndependentPairs (V := V)).image binaryPairSpan

/-- The span of an independent binary pair has dimension two. -/
theorem finrank_binaryPairSpan
    (s : {s : Fin 2 → V // LinearIndependent (ZMod 2) s}) :
    Module.finrank (ZMod 2) (binaryPairSpan s) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (finrank_span_eq_card s.property).trans (Fintype.card_fin 2)

/-- At most six independent ordered pairs span one binary two-dimensional
subspace: they are ordered bases of that subspace. -/
theorem card_binaryPairSpan_fiber_le_six [Finite V]
    (Φ : Submodule (ZMod 2) V) :
    ((binaryIndependentPairs (V := V)).filter fun s ↦ binaryPairSpan s = Φ).card ≤ 6 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype Φ := Fintype.ofFinite Φ
  let A := (binaryIndependentPairs (V := V)).filter fun s ↦ binaryPairSpan s = Φ
  by_cases hA : A.Nonempty
  · obtain ⟨s, hsA⟩ := hA
    have hsΦ : binaryPairSpan (s : {t : Fin 2 → V // LinearIndependent (ZMod 2) t}) = Φ :=
      (Finset.mem_filter.mp hsA).2
    have hΦrank : Module.finrank (ZMod 2) Φ = 2 := by
      rw [← hsΦ]
      exact finrank_binaryPairSpan s
    let liftPair : {s // s ∈ A} →
        {t : Fin 2 → Φ // LinearIndependent (ZMod 2) t} := fun s ↦
      ⟨fun i ↦ ⟨s.1.1 i, by
          have hi : s.1.1 i ∈ binaryPairSpan s.1 :=
            Submodule.subset_span (Set.mem_range_self i)
          have hspan : binaryPairSpan s.1 = Φ := (Finset.mem_filter.mp s.2).2
          simpa [hspan] using hi⟩,
        by
          apply LinearIndependent.of_comp Φ.subtype
          change LinearIndependent (ZMod 2) s.1.1
          exact s.1.2⟩
    have hlift : Function.Injective liftPair := by
      intro s t h
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact congrArg (fun u ↦ ((u.1 i : Φ) : V)) h
    calc
      A.card = Fintype.card {s // s ∈ A} := (Fintype.card_coe A).symm
      _ ≤ Fintype.card {t : Fin 2 → Φ // LinearIndependent (ZMod 2) t} :=
        Fintype.card_le_of_injective liftPair hlift
      _ = 6 := by
        rw [← Nat.card_eq_fintype_card, card_linearIndependent (by omega)]
        simp [hΦrank, Fin.prod_univ_two]
  · simp only [Finset.not_nonempty_iff_eq_empty] at hA
    simp [A, hA]

/-- There are at least `(2^d-1)(2^d-2)/6` binary two-dimensional
subspaces in dimension `d`. -/
theorem pair_span_count_lower_bound [Finite V]
    (hdim : 2 ≤ Module.finrank (ZMod 2) V) :
    (2 ^ Module.finrank (ZMod 2) V - 1) *
          (2 ^ Module.finrank (ZMod 2) V - 2) / 6 ≤
      (binaryPairSpans (V := V)).card := by
  classical
  have hcount := card_le_card_image_mul_of_fiber_le
    (binaryIndependentPairs (V := V)) binaryPairSpan 6
    (fun Φ _ ↦ card_binaryPairSpan_fiber_le_six Φ)
  rw [card_binaryIndependentPairs hdim] at hcount
  have hcount' :
      (2 ^ Module.finrank (ZMod 2) V - 1) *
          (2 ^ Module.finrank (ZMod 2) V - 2) ≤
        6 * (binaryPairSpans (V := V)).card := by
    simpa [binaryPairSpans, Nat.mul_comm] using hcount
  exact Nat.div_le_of_le_mul hcount'

end IndependentPairs

section CodimensionTwo

variable {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Finite B]

/-- The prescribed-domain additive subgroups obtained as common kernels of
independent pairs of binary linear functionals. -/
noncomputable def codimTwoBinarySubspaces (D : AddSubgroup B) :
    Finset (AddSubgroup B) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  exact (binaryPairSpans (V := Module.Dual (ZMod 2) D)).image fun Φ ↦
    ambientBinarySubspace D Φ.dualCoannihilator

/-- Dual coannihilation, followed by inclusion in the ambient group, is
injective on binary functional subspaces. -/
theorem ambient_dualCoannihilator_injective (D : AddSubgroup B) :
    Function.Injective (fun Φ : Submodule (ZMod 2) (Module.Dual (ZMod 2) D) ↦
      ambientBinarySubspace D Φ.dualCoannihilator) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Φ Ψ h
  have hco : Φ.dualCoannihilator = Ψ.dualCoannihilator :=
    ambientBinarySubspace_injective D h
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ),
    ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Ψ), hco]

/-- A binary `d`-space has at least `(2^d-1)(2^d-2)/6` distinct
codimension-two subspaces, represented as ambient additive subgroups. -/
theorem codimTwoBinarySubspaces_count_lower_bound
    (D : AddSubgroup B) (hdim : 2 ≤ Module.finrank (ZMod 2) D) :
    (Nat.card D - 1) * (Nat.card D - 2) / 6 ≤
      (codimTwoBinarySubspaces D).card := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  have h := pair_span_count_lower_bound
    (V := Module.Dual (ZMod 2) D)
    (by simpa [Subspace.dual_finrank_eq] using hdim)
  have hcard :
      2 ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) D) = Nat.card D := by
    rw [Subspace.dual_finrank_eq, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]
    congr 1
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [hcard] at h
  simpa [codimTwoBinarySubspaces,
    Finset.card_image_of_injective _ (ambient_dualCoannihilator_injective D)] using h

/-- Every subgroup in the codimension-two family lies inside the prescribed
domain. -/
theorem codimTwoBinarySubspaces_le (D : AddSubgroup B) (W : AddSubgroup B)
    (hW : W ∈ codimTwoBinarySubspaces D) : W ≤ D := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  rw [codimTwoBinarySubspaces, Finset.mem_image] at hW
  obtain ⟨Φ, _, rfl⟩ := hW
  exact ambientBinarySubspace_le D Φ.dualCoannihilator

/-- Every subgroup in the codimension-two family has one quarter as many
elements as the prescribed domain. -/
theorem natCard_codimTwoBinarySubspace (D : AddSubgroup B) (W : AddSubgroup B)
    (hW : W ∈ codimTwoBinarySubspaces D) :
    Nat.card W = Nat.card D / 4 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite (Module.Dual (ZMod 2) D) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) D ↦ (f : D → ZMod 2))
      LinearMap.coe_injective
  rw [codimTwoBinarySubspaces, Finset.mem_image] at hW
  obtain ⟨Φ, hΦ, rfl⟩ := hW
  rw [binaryPairSpans, Finset.mem_image] at hΦ
  obtain ⟨s, _, rfl⟩ := hΦ
  rw [natCard_ambientBinarySubspace]
  have hrank := Subspace.finrank_add_finrank_dualCoannihilator_eq (binaryPairSpan s)
  rw [finrank_binaryPairSpan] at hrank
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [htwo]
  have hpow :
      2 ^ Module.finrank (ZMod 2) D =
        4 * 2 ^ Module.finrank (ZMod 2) (binaryPairSpan s).dualCoannihilator := by
    rw [← hrank, pow_add]
    norm_num
  rw [hpow, Nat.mul_comm 4, Nat.mul_div_left]
  positivity

/-- Two binary subspaces inside the same finite domain satisfy the usual
product/intersection cardinality inequality. -/
theorem binary_subspace_card_mul_le_inf_mul_domain
    (D W₁ W₂ : AddSubgroup B) (h₁ : W₁ ≤ D) (h₂ : W₂ ≤ D) :
    Nat.card W₁ * Nat.card W₂ ≤ Nat.card ↥(W₁ ⊓ W₂) * Nat.card D := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₁ : Submodule (ZMod 2) B := AddSubgroup.toZModSubmodule 2 W₁
  let U₂ : Submodule (ZMod 2) B := AddSubgroup.toZModSubmodule 2 W₂
  let T : Submodule (ZMod 2) B := AddSubgroup.toZModSubmodule 2 D
  have hsup : U₁ ⊔ U₂ ≤ T := sup_le (show U₁ ≤ T by exact h₁) (show U₂ ≤ T by exact h₂)
  have hdim_sup : Module.finrank (ZMod 2) ↥(U₁ ⊔ U₂) ≤
      Module.finrank (ZMod 2) T := Submodule.finrank_mono hsup
  have hdim_eq := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
  have hdim : Module.finrank (ZMod 2) U₁ + Module.finrank (ZMod 2) U₂ ≤
      Module.finrank (ZMod 2) ↥(U₁ ⊓ U₂) + Module.finrank (ZMod 2) T := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hdim
  simp only [pow_add] at hp
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  have hc₁ := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U₁)
  have hc₂ := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U₂)
  have hci := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(U₁ ⊓ U₂))
  have hcT := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := T)
  rw [htwo] at hc₁ hc₂ hci hcT
  rw [← hc₁, ← hc₂, ← hci, ← hcT] at hp
  simpa [U₁, U₂, T] using hp

/-- In the quadratic construction, two size-`4K` subspaces of a size-`16K`
domain intersect in at least `K` points. -/
theorem card_le_inf_of_card_eq_four_mul
    (D W₁ W₂ : AddSubgroup B) (K : ℕ) (hK : 0 < K)
    (hD : Nat.card D = 16 * K)
    (hW₁ : Nat.card W₁ = 4 * K) (hW₂ : Nat.card W₂ = 4 * K)
    (hle₁ : W₁ ≤ D) (hle₂ : W₂ ≤ D) :
    K ≤ Nat.card ↥(W₁ ⊓ W₂) := by
  have h := binary_subspace_card_mul_le_inf_mul_domain D W₁ W₂ hle₁ hle₂
  rw [hD, hW₁, hW₂] at h
  nlinarith

end CodimensionTwo

end BinaryFieldCounterexamples
