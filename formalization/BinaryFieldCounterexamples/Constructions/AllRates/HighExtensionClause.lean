/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.BaseClauses
public import BinaryFieldCounterexamples.Constructions.AllRates.ExtensionPadding

/-!
# The arbitrary-rate high-extension clause

A field extension large enough to realize the independent cancellation
parameters supplies an injective actual subgroup-challenge population. Uniform
rounding and padding on every prescribed binary domain yield both exact individual
agreements and the original containing-field probability bound.
-/

@[expose] public section
universe u v
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An actual injective challenge population directly dominates the required
collision-probability expression, uniformly in the containing field size. -/
theorem allRate_probability_of_injective_population (q N M b s : ℕ) (C : ℝ)
    (hq : 0<q) (hN : 0<N) (hM : 0<M) (hC : 0<C)
    (hpopulation : (N:ℝ)^s/C≤M) (hb : M≤b) :
    1/(1+C*q/(N:ℝ)^s)-1/q≤(b:ℝ)/q := by
  have hceil : ⌈((q*M:ℕ):ℚ)/(q+M-1:ℕ)⌉₊≤M := by
    apply Nat.ceil_le.mpr
    have hden : (0:ℚ)<q+M-1 := by
      have hq' : (0:ℚ)<q := by exact_mod_cast hq
      have hM' : (1:ℚ)≤M := by exact_mod_cast hM
      linarith
    rw [Nat.cast_mul,Nat.cast_sub (show 1≤q+M by omega),Nat.cast_add,Nat.cast_one]
    apply (div_le_iff₀ hden).mpr
    have hM' : (1:ℚ)≤M := by exact_mod_cast hM
    nlinarith
  exact allRate_probability_bound q N M M b s C hq hN hM hC hpopulation hceil (by omega)
/-- The high-extension finite construction gives the original fourth clause
uniformly over every prescribed domain and every field embedding. -/
theorem all_rate_high_extension (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ N0 : ℕ, ∀ (B : Type u) (F : Type v) [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] (φ : B →+* F) (D : AddSubgroup B),
      N0≤(additiveDomain D).card → Fintype.card B^(s+1)≤Fintype.card F →
      let S := mappedDomain φ (additiveDomain D)
      let N := S.card
      let J := ⌊ρ*N⌋₊
      ∃ f g : S → F, agreementEQ S J f J ∧ agreementEQ S J g J ∧
        commonAgreementEQ S J f g J ∧
        (1/(1+(2:ℝ)^((ell+s)*s)*Fintype.card F/(N:ℝ)^s)-1/Fintype.card F)≤
          ((nonzeroBadChallenges S J f g
            ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊).card:ℝ)/Fintype.card F := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_dimension_cutoff ρ hρ hρ' ell s hlow hroom
  refine ⟨2^d0,?_⟩
  intro B F _ _ _ _ _ φ D hN hsize
  let : Algebra B F := φ.toAlgebra
  let : CharP F 2 := charP_of_injective_ringHom φ.injective 2
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  obtain ⟨d,hD⟩ := allRate_domain_card_power D
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hd : d0≤d := by
    rw [hcard] at hN
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hN
  have hdim : ell+2*s+2≤d := hd0.trans hd
  obtain ⟨H,hHD,hH⟩ := exists_binary_subspace_card_eq D (2^(d-ell)) ⟨d-ell,rfl⟩ (by
    rw [hD]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
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
  have hp := AllRatesConstruction.exists_all_rate_highExtension_padded_pair D H (d-ell-s) s ⌊ρ*(2:ℝ)^d⌋₊
    ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊ hs (by omega) hH' hHD hJ
    (by rwa [hD]) (by rwa [hD,hH]) hT hsize
  have halg : algebraMap B F=φ := RingHom.algebraMap_toAlgebra φ
  have hdom : additiveDomain (D.map (algebraMap B F).toAddMonoidHom)=
      mappedDomain φ (additiveDomain D) := by rw [halg,←mappedDomain_additiveDomain]
  dsimp only at hp
  rw [hdom] at hp
  obtain ⟨f,g,hf,hg,hcommon,hcount⟩ := hp
  dsimp only
  rw [card_mappedDomain,hcard]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨f,g,hf,hg,hcommon,?_⟩
  have hpop : (((2^d:ℕ):ℝ)^s)/(2:ℝ)^((ell+s)*s)≤((2^((d-ell-s)*s):ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact (all_rate_power_parameters d ell s (by omega)).2.2.symm.le
  have hprob := allRate_probability_of_injective_population (Fintype.card F) (2^d)
    (2^((d-ell-s)*s)) _ s ((2:ℝ)^((ell+s)*s)) Fintype.card_pos (by positivity)
    (by positivity) (by positivity) hpop hcount
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hprob
end BinaryFieldCounterexamples
