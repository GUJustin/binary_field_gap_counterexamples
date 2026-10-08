/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.PowerParameters
public import BinaryFieldCounterexamples.Constructions.AllRates.FinitePadding
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Agreement.Domains

/-!
# Uniform finite pairs on prescribed binary domains

A uniform dimension cutoff supplies rounding and padding room. Inside every
prescribed additive domain, an actual binary subspace of the required dyadic
size supports the concrete seed; nodal padding yields the exact requested
message length, threshold, collision ceiling, and full decoding list.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A uniform dimension cutoff gives concrete arbitrary-rate pairs on every
prescribed binary domain, keeping the exact finite pooling ceiling. -/
theorem exists_all_rate_domain_pair_cutoff (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ d0 : ℕ, ell+2*s+2≤d0 ∧ ∀ d : ℕ, d0≤d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] (D : AddSubgroup F),
      Nat.card D=2^d →
      let E := additiveDomain D
      let J := ⌊ρ*(2:ℝ)^d⌋₊
      let T := ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊
      let M := 2^((d-ell-s)*s)
      ∃ f g : E → F, commonAgreementEQ E J f g J ∧
        ⌈((Fintype.card F*M:ℕ):ℚ)/(Fintype.card F+M-1:ℕ)⌉₊≤
          (badChallenges E J f g T).card ∧
        ordinaryList E (J+1) T (badChallenges E J f g T).card := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_dimension_cutoff ρ hρ hρ' ell s hlow hroom
  refine ⟨d0,hd0,?_⟩
  intro d hd F _ _ _ D hD
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hdim : ell+2*s+2≤d := hd0.trans hd
  obtain ⟨H,hHD,hH⟩ := exists_binary_subspace_card_eq D (2^(d-ell)) ⟨d-ell,rfl⟩ (by
    rw [hD]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hcardH : (additiveDomain H).card=2^(d-ell) := by rw [card_additiveDomain,hH]
  have hsub : additiveDomain H ⊆ additiveDomain D := by
    intro x hx
    exact (mem_additiveDomain D x).mpr (hHD ((mem_additiveDomain H x).mp hx))
  have hH' : Nat.card H=2^((d-ell-s)+s) := by
    rw [hH]
    congr 1
    omega
  have hpow : 2*2^(d-ell-s-2)=(2:ℕ)^(d-ell-s-1) := by
    rw [mul_comm,←pow_succ]
    congr 1
    omega
  obtain ⟨hJ,hroom',hT,hJD⟩ := hcut d hd
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hJ hroom' hT hJD
  rw [hpow] at hJ hroom' hT
  dsimp only
  apply exists_all_rate_finite_padded_pair (additiveDomain D) H (d-ell-s) s
    ⌊ρ*(2:ℝ)^d⌋₊ ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊ hs
    (by omega) hH' hsub hJ
  · rwa [hcard]
  · rwa [hcard,hcardH]
  · exact hT
end BinaryFieldCounterexamples
