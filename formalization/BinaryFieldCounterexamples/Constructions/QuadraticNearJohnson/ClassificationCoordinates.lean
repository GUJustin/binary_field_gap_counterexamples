/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SharpSource
/-!
# Coordinate reduction for exact quadratic-line classification

Any strict-degree explaining polynomial on more than 2K base-field coordinates forces
the challenge into the span of 1 and the fixed exterior coefficient. The same
two coordinate projections give base-field explaining polynomials of strict degree K;
their mapped sum recovers the entire original explaining polynomial.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- More than 2K agreements force a two-coordinate challenge and explaining polynomial. -/
theorem quadratic_classification_coordinates
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (θ : F) (hθ : θ ∉ Set.range (algebraMap B F))
    (K : ℕ) (hK : 2 ≤ K) (S : Finset B) (hS : 2 * K < S.card)
    (p : F[X]) (hp : p.degree < K) (z : F)
    (heval : ∀ x ∈ S, p.eval (algebraMap B F x) =
      (algebraMap B F x) ^ (8*K-1) + θ * (algebraMap B F x) ^ (4*K-1) +
        z * (algebraMap B F x) ^ (2*K-1)) :
    ∃ z0 a : B, ∃ h0 h1 : B[X],
      z = algebraMap B F z0 + θ * algebraMap B F a ∧
      h0.degree < K ∧ h1.degree < K ∧
      (∀ x ∈ S, h0.eval x = x^(8*K-1) + z0*x^(2*K-1)) ∧
      (∀ x ∈ S, h1.eval x = x^(4*K-1) + a*x^(2*K-1)) := by
  classical
  let T : Submodule B F := Submodule.span B ({1, θ} : Set F)
  have hz : z ∈ T := by
    by_contra hz
    obtain ⟨l, hl, hlz⟩ := LinearMap.exists_extend_of_notMem (0 : T →ₗ[B] B) hz 1
    have hzero (x : F) (hx : x ∈ T) : l x = 0 := by
      have he := congrArg (fun f : T →ₗ[B] B ↦ f ⟨x, hx⟩) hl
      simpa using he
    have hl1 : l 1 = 0 := hzero 1 (Submodule.subset_span (by simp))
    have hlθ : l θ = 0 := hzero θ (Submodule.subset_span (by simp))
    have hb := quadratic_source_agreementLE_of_projection S K (by omega) θ z l hl1 hlθ hlz p hp
    rw [agreementCount_mappedDomain (algebraMap B F) S
      (fun x ↦ x ^ (8*K-1) + θ*x^(4*K-1) + z*x^(2*K-1)) p] at hb
    have hf : (S.filter fun x ↦ p.eval (algebraMap B F x) =
        (algebraMap B F x) ^ (8*K-1) + θ * (algebraMap B F x) ^ (4*K-1) +
          z * (algebraMap B F x) ^ (2*K-1)) = S := Finset.filter_eq_self.mpr heval
    rw [hf] at hb
    omega
  obtain ⟨z0, a, hza⟩ := Submodule.mem_span_pair.mp hz
  have hrepr : z = algebraMap B F z0 + θ * algebraMap B F a := by
    simpa [Algebra.smul_def, mul_comm] using hza.symm
  obtain ⟨l0, l1, hl01, hl0θ, hl11, hl1θ⟩ := exists_extension_coordinates θ hθ
  obtain ⟨h0, hh0, he0⟩ := exists_projected_polynomial l0 K p hp
  obtain ⟨h1, hh1, he1⟩ := exists_projected_polynomial l1 K p hp
  have hl0 (b : B) : l0 (algebraMap B F b) = b := by
    simpa [hl01] using linearMap_apply_algebraMap_mul l0 b 1
  have hl1 (b : B) : l1 (algebraMap B F b) = 0 := by
    simpa [hl11] using linearMap_apply_algebraMap_mul l1 b 1
  have hl0z : l0 z = z0 := by
    rw [hrepr, map_add, hl0, mul_comm θ, linearMap_apply_algebraMap_mul, hl0θ]
    simp
  have hl1z : l1 z = a := by
    rw [hrepr, map_add, hl1, mul_comm θ, linearMap_apply_algebraMap_mul, hl1θ]
    simp
  refine ⟨z0, a, h0, h1, hrepr, hh0, hh1, ?_, ?_⟩
  · intro x hx
    rw [he0, heval x hx]
    simp only [map_add, ← map_pow, hl0]
    rw [mul_comm θ, mul_comm z, linearMap_apply_algebraMap_mul,
      linearMap_apply_algebraMap_mul, hl0θ, hl0z]
    ring
  · intro x hx
    rw [he1, heval x hx]
    simp only [map_add, ← map_pow, hl1]
    rw [mul_comm θ, mul_comm z, linearMap_apply_algebraMap_mul,
      linearMap_apply_algebraMap_mul, hl1θ, hl1z]
    ring

/-- The two projected explaining polynomials recover the entire original polynomial. -/
theorem quadratic_classification_reconstruct
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (θ : F) (K : ℕ) (hK : 2 ≤ K) (S : Finset B) (hS : 2*K < S.card)
    (p : F[X]) (hp : p.degree < K) (z : F) (z0 a : B) (h0 h1 : B[X])
    (hh0 : h0.degree < K) (hh1 : h1.degree < K)
    (hz : z = algebraMap B F z0 + θ * algebraMap B F a)
    (heval : ∀ x ∈ S, p.eval (algebraMap B F x) =
      (algebraMap B F x)^(8*K-1) + θ*(algebraMap B F x)^(4*K-1) +
        z*(algebraMap B F x)^(2*K-1))
    (he0 : ∀ x ∈ S, h0.eval x = x^(8*K-1) + z0*x^(2*K-1))
    (he1 : ∀ x ∈ S, h1.eval x = x^(4*K-1) + a*x^(2*K-1)) :
    p = h0.map (algebraMap B F) + C θ * h1.map (algebraMap B F) := by
  classical
  have hpN : p.natDegree < K := by
    by_cases hz : p = 0
    · simp [hz]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr hp
  have h0N : h0.natDegree < K := by
    by_cases hz : h0 = 0
    · simp [hz]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr hh0
  have h1N : h1.natDegree < K := by
    by_cases hz : h1 = 0
    · simp [hz]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr hh1
  apply eq_of_natDegree_lt_card_of_eval_eq p _
    (f := fun x : S ↦ algebraMap B F (x : B))
    ((algebraMap B F).injective.comp Subtype.val_injective)
  · intro x
    rw [heval x x.property]
    simp only [eval_add, eval_mul, eval_C, eval_map_apply, he0 x x.property,
      he1 x x.property, map_add, map_mul, map_pow, hz]
    ring
  · have hq := natDegree_add_le (h0.map (algebraMap B F))
        (C θ * h1.map (algebraMap B F))
    have hm0 := (natDegree_map_le (p := h0) (f := algebraMap B F))
    have hm1 := (natDegree_map_le (p := h1) (f := algebraMap B F))
    have hc := natDegree_C_mul_le θ (h1.map (algebraMap B F))
    rw [Fintype.card_coe]
    omega
end BinaryFieldCounterexamples
