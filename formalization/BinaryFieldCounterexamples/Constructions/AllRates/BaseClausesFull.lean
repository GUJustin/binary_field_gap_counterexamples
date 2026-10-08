/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.DomainPairFull
public import BinaryFieldCounterexamples.Counting.AllRateBounds
public import BinaryFieldCounterexamples.Constructions.AllRates.BaseClauses

/-!
# Uniform probability and saturation for arbitrary rates

For fixed dyadic parameters, the concrete finite-domain construction proves
both original base-field clauses: the real nonzero-challenge probability bound
and full finite-field saturation under polynomial field-size growth. Both
clauses keep their full list-decoding guarantees and use the same parameters.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4.5 part 1 and its closing list clause: uniform probability, exact second-input agreement, and a decoding list pinned to the first input. -/
theorem all_rate_base_probability_full (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ N0 : ℕ, ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
      (D : AddSubgroup F), N0≤(additiveDomain D).card →
      let S := additiveDomain D
      let N := S.card
      let J := ⌊ρ*N⌋₊
      let T := ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊
      ∃ f g : S → F, agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
        (1/(1+(2:ℝ)^((ell+s)*s)*Fintype.card F/(N:ℝ)^s)-1/Fintype.card F)≤
          ((nonzeroBadChallenges S J f g T).card:ℝ)/Fintype.card F ∧
        (∃ ps : Finset F[X], (badChallenges S J f g T).card = ps.card ∧
          ∀ p ∈ ps, p.degree < J+1 ∧ T ≤ agreementCount S f p) := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_domain_pair_cutoff_full ρ hρ hρ' ell s hs hlow hroom
  refine ⟨2^d0,?_⟩
  intro F _ _ _ D hN
  obtain ⟨d,hD⟩ := allRate_domain_card_power D
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hd : d0≤d := by
    rw [hcard] at hN
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hN
  obtain ⟨f,g,hg,hcommon,hbad,hlist⟩ := hcut d hd F D hD
  dsimp only
  simp only [hcard,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨f,g,hg,hcommon,?_,hlist⟩
  have hpop : (((2^d:ℕ):ℝ)^s)/(2:ℝ)^((ell+s)*s)≤((2^((d-ell-s)*s):ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact (all_rate_power_parameters d ell s (by omega)).2.2.symm.le
  have hpred := card_badChallenges_sub_one_le_nonzero (additiveDomain D)
    ⌊ρ*(2:ℝ)^d⌋₊ f g ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊
  have hb0 : (badChallenges (additiveDomain D) ⌊ρ*(2:ℝ)^d⌋₊ f g
      ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊).card≤
      (nonzeroBadChallenges (additiveDomain D) ⌊ρ*(2:ℝ)^d⌋₊ f g
      ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊).card+1 := by omega
  have hp := allRate_probability_bound (Fintype.card F) (2^d) (2^((d-ell-s)*s)) _ _ s
    ((2:ℝ)^((ell+s)*s)) Fintype.card_pos (by positivity) (by positivity) (by positivity)
    hpop hbad hb0
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hp
/-- Theorem 4.5 part 2 and its closing list clause: finite-field saturation, exact second-input agreement, and a decoding list pinned to the first input. -/
theorem all_rate_base_saturation_full (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2))))
    (a : ℝ) (has : 2*a<s) :
    ∃ N1 : ℕ, ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
      (D : AddSubgroup F), N1≤(additiveDomain D).card →
      (Fintype.card F:ℝ)≤((additiveDomain D).card:ℝ)^a →
      let S := additiveDomain D
      let N := S.card
      let J := ⌊ρ*N⌋₊
      let T := ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊
      ∃ f g : S → F, agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
        badChallenges S J f g T=Finset.univ ∧
        (∃ ps : Finset F[X], Fintype.card F = ps.card ∧
          ∀ p ∈ ps, p.degree < J+1 ∧ T ≤ agreementCount S f p) := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_domain_pair_cutoff_full ρ hρ hρ' ell s hs hlow hroom
  obtain ⟨N1,hN11,hsat⟩ := allRate_eventual_pooling_ceil_eq_field_size a
    ((2:ℝ)^((ell+s)*s)) s (by positivity) has
  refine ⟨max (2^d0) N1,?_⟩
  intro F _ _ _ D hN hq
  obtain ⟨d,hD⟩ := allRate_domain_card_power D
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hd : d0≤d := by
    have he : 2^d0≤2^d := by rw [←hcard]; exact (le_max_left _ _).trans hN
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp he
  obtain ⟨f,g,hg,hcommon,hbad,hlist⟩ := hcut d hd F D hD
  have hpop : (((2^d:ℕ):ℝ)^s)/(2:ℝ)^((ell+s)*s)≤((2^((d-ell-s)*s):ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact (all_rate_power_parameters d ell s (by omega)).2.2.symm.le
  have hN1 : N1≤2^d := by rw [←hcard]; exact (le_max_right _ _).trans hN
  have he := hsat (2^d) hN1 (Fintype.card F) (2^((d-ell-s)*s)) Fintype.card_pos
    (by simpa only [hcard] using hq) hpop
  rw [he] at hbad
  have hbadcard : (badChallenges (additiveDomain D) ⌊ρ*(2:ℝ)^d⌋₊ f g
      ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*(2:ℝ)^d⌉₊).card=Fintype.card F :=
    le_antisymm (Finset.card_le_univ _) hbad
  dsimp only
  simp only [hcard,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨f,g,hg,hcommon,Finset.eq_univ_of_card _ hbadcard,?_⟩
  rwa [hbadcard] at hlist
end BinaryFieldCounterexamples
