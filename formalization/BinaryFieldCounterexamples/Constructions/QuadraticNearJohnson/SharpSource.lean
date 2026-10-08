/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SourceBound
public import Mathlib.FieldTheory.Finiteness

/-!
# Sharp individual agreement in extensions of degree at least three

A functional killing `1` and `θ`, but taking the shift of the first input to `1`,
projects every explaining polynomial of the first word onto an explaining polynomial of the
second monomial. This proves the sharp upper bound without changing any challenges.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Cardinality at least the cube of the base-field cardinality supplies an
exterior element and a third coordinate functional. -/
theorem exists_quadratic_sharp_coordinates
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (hext : Fintype.card B ^ 3 ≤ Fintype.card F) :
    ∃ θ s : F, θ ∉ Set.range (algebraMap B F) ∧
      ∃ l : F →ₗ[B] B, l 1 = 0 ∧ l θ = 0 ∧ l s = 1 := by
  classical
  have hb : 1 < Fintype.card B := Fintype.one_lt_card
  have hproper : ¬ Function.Surjective (algebraMap B F) := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective (algebraMap B F) hsurj
    have hlt : Fintype.card B < Fintype.card B ^ 3 := by
      simpa using Nat.pow_lt_pow_right hb (by decide : 1 < 3)
    omega
  have hex : ∃ θ : F, θ ∉ Set.range (algebraMap B F) := by
    simpa only [Function.Surjective, not_forall, Set.mem_range] using hproper
  obtain ⟨θ, hθ⟩ := hex
  have hrank : 3 ≤ Module.finrank B F := by
    rw [Module.card_eq_pow_finrank (K := B) (V := F)] at hext
    exact (Nat.pow_le_pow_iff_right hb).mp hext
  let T : Submodule B F := Submodule.span B (Set.range ![1, θ])
  have hTdim : Module.finrank B T ≤ 2 := by
    simpa only [Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := B) ![(1 : F), θ])
  have hTne : T ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hTdim
    omega
  have hexs : ∃ s : F, s ∉ T := by
    by_contra! h
    apply hTne
    ext x
    simp [h x]
  obtain ⟨s, hs⟩ := hexs
  obtain ⟨l, hl, hls⟩ := LinearMap.exists_extend_of_notMem (0 : T →ₗ[B] B) hs 1
  have hzero (x : F) (hx : x ∈ T) : l x = 0 := by
    have he := congrArg (fun f : T →ₗ[B] B ↦ f ⟨x, hx⟩) hl
    simpa using he
  refine ⟨θ, s, hθ, l, hzero 1 ?_, hzero θ ?_, hls⟩
  · exact Submodule.subset_span ⟨0, by simp⟩
  · exact Submodule.subset_span ⟨1, by simp⟩

/-- A third coordinate projection bounds the first input by the second
monomial's root count on the literal mapped domain. -/
theorem quadratic_source_agreementLE_of_projection
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K : ℕ) (hK : 1 ≤ K) (θ s : F)
    (l : F →ₗ[B] B) (hl1 : l 1 = 0) (hlθ : l θ = 0) (hls : l s = 1) :
    agreementLE (mappedDomain (algebraMap B F) D) K
      (fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1) +
        s * (x : F) ^ (2 * K - 1)) (2 * K - 1) := by
  classical
  intro p hp
  obtain ⟨q, hq, heq⟩ := exists_projected_polynomial l K p hp
  have hlbase (b : B) : l (algebraMap B F b) = 0 := by
    simpa [hl1] using linearMap_apply_algebraMap_mul l b 1
  rw [agreementCount_mappedDomain (algebraMap B F) D
    (fun x ↦ x ^ (8 * K - 1) + θ * x ^ (4 * K - 1) + s * x ^ (2 * K - 1)) p]
  have hsub : (D.filter fun x ↦ p.eval (algebraMap B F x) =
      (algebraMap B F x) ^ (8 * K - 1) + θ * (algebraMap B F x) ^ (4 * K - 1) +
        s * (algebraMap B F x) ^ (2 * K - 1)) ⊆
      D.filter (fun x ↦ q.eval x = x ^ (2 * K - 1)) := by
    intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    rw [heq, hx]
    simp only [map_add, ← map_pow, hlbase]
    rw [mul_comm θ, mul_comm s, linearMap_apply_algebraMap_mul,
      linearMap_apply_algebraMap_mul, hlθ, hls]
    simp
  apply (Finset.card_le_card hsub).trans
  have hdegree : (K : WithBot ℕ) ≤ (X ^ (2 * K - 1) : B[X]).degree := by
    rw [degree_X_pow]
    exact_mod_cast (show K ≤ 2 * K - 1 by omega)
  have hbound := agreementLE_polynomial D K (X ^ (2 * K - 1) : B[X]) hdegree q hq
  rw [agreementCount_eq_card_filter D (fun x ↦ (X ^ (2 * K - 1) : B[X]).eval x) q] at hbound
  simpa using hbound

end BinaryFieldCounterexamples
