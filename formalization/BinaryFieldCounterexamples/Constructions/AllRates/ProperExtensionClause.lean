/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.BaseClauses
public import BinaryFieldCounterexamples.Agreement.SourceConversionPair

/-!
# The arbitrary-rate proper-extension clause

The checked conversion of Lemma 3.12 keeps every old exceptional challenge while making
both individual agreements equal to the old common agreement. The exact probability
bound therefore transfers with the same domain-size cutoff and constants.
-/

@[expose] public section
universe u v
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The conversion of Lemma 3.12 transfers the quantitative probability bound while
making both individual agreements equal to the old exact common agreement. -/
theorem converted_pair_of_probability_bound
    {B : Type u} {F : Type v} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B →+* F) (hsize : Fintype.card B<Fintype.card F)
    (D : Finset B) (K T s : ℕ) (C : ℝ) (f g : D → B)
    (hcommon : commonAgreementEQ D K f g K)
    (hprob : 1/(1+C*Fintype.card B/(D.card:ℝ)^s)-1/Fintype.card B≤
      ((nonzeroBadChallenges D K f g T).card:ℝ)/Fintype.card B) :
    ∃ u v : mappedDomain φ D → F,
      agreementEQ (mappedDomain φ D) K u K ∧
      agreementEQ (mappedDomain φ D) K v K ∧
      commonAgreementEQ (mappedDomain φ D) K u v K ∧
      (Fintype.card B:ℝ)/(1+C*Fintype.card B/(D.card:ℝ)^s)-1≤
        (nonzeroBadChallenges (mappedDomain φ D) K u v T).card := by
  obtain ⟨u,v,hu,hv,hcommon',hcount⟩ :=
    exists_converted_pair_of_common_agreement φ hsize D K K T f g hcommon
  refine ⟨u,v,hu,hv,hcommon',?_⟩
  have hq : (0:ℝ)<Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hp := mul_le_mul_of_nonneg_right hprob hq.le
  have hlower : (Fintype.card B:ℝ)/(1+C*Fintype.card B/(D.card:ℝ)^s)-1≤
      (nonzeroBadChallenges D K f g T).card := by
    convert hp using 1 <;> field_simp
  have hsub : (nonzeroBadChallenges D K f g T).card≤(badChallenges D K f g T).card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  exact hlower.trans (by exact_mod_cast hsub.trans hcount)
/-- Any uniform base probability clause transfers to the original proper
extension clause with exactly the same cutoff and constants. -/
theorem all_rate_proper_extension_of_base_clause (ρ α C : ℝ) (s N0 : ℕ)
    (hbase : ∀ (B : Type u) [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B),
      N0≤(additiveDomain D).card →
      let S := additiveDomain D
      let N := S.card
      let J := ⌊ρ*N⌋₊
      let T := ⌈α*N⌉₊
      ∃ f g : S → B, commonAgreementEQ S J f g J ∧
        1/(1+C*Fintype.card B/(N:ℝ)^s)-1/Fintype.card B≤
          ((nonzeroBadChallenges S J f g T).card:ℝ)/Fintype.card B) :
    ∀ (B : Type u) (F : Type v) [Field B] [Fintype B] [CharP B 2] [Field F] [Fintype F]
      (φ : B →+* F) (D : AddSubgroup B),
      N0≤(additiveDomain D).card → Fintype.card B<Fintype.card F →
      let S := mappedDomain φ (additiveDomain D)
      let N := S.card
      let J := ⌊ρ*N⌋₊
      ∃ f g : S → F, agreementEQ S J f J ∧ agreementEQ S J g J ∧
        commonAgreementEQ S J f g J ∧
        (Fintype.card B:ℝ)/(1+C*Fintype.card B/(N:ℝ)^s)-1≤
          (nonzeroBadChallenges S J f g ⌈α*N⌉₊).card := by
  intro B F _ _ _ _ _ φ D hN hsize
  obtain ⟨f,g,hcommon,hprob⟩ := hbase B D hN
  dsimp only
  rw [card_mappedDomain]
  exact converted_pair_of_probability_bound φ hsize (additiveDomain D)
    ⌊ρ*(additiveDomain D).card⌋₊ ⌈α*(additiveDomain D).card⌉₊ s C f g hcommon hprob
/-- The proved fixed-dyadic base construction supplies the complete original
proper-extension clause with the same explicit threshold and constant. -/
theorem all_rate_proper_extension (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ N0 : ℕ, ∀ (B : Type u) (F : Type v) [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] (φ : B →+* F) (D : AddSubgroup B),
      N0≤(additiveDomain D).card → Fintype.card B<Fintype.card F →
      let S := mappedDomain φ (additiveDomain D)
      let N := S.card
      let J := ⌊ρ*N⌋₊
      ∃ f g : S → F, agreementEQ S J f J ∧ agreementEQ S J g J ∧
        commonAgreementEQ S J f g J ∧
        (Fintype.card B:ℝ)/(1+(2:ℝ)^((ell+s)*s)*Fintype.card B/(N:ℝ)^s)-1≤
          (nonzeroBadChallenges S J f g
            ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊).card := by
  obtain ⟨N0,hbase⟩ := all_rate_base_probability.{u} ρ hρ hρ' ell s hs hlow hroom
  refine ⟨N0,all_rate_proper_extension_of_base_clause ρ
    (ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))) ((2:ℝ)^((ell+s)*s)) s N0 ?_⟩
  intro B _ _ _ D hN
  obtain ⟨f,g,hc,hp,hl⟩ := hbase B D hN
  exact ⟨f,g,hc,hp⟩
end BinaryFieldCounterexamples
