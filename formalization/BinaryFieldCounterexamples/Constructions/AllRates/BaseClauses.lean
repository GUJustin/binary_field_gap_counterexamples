/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.DomainPair
public import BinaryFieldCounterexamples.Counting.AllRateBounds

/-!
# Uniform probability and saturation for arbitrary rates

For fixed dyadic parameters, the concrete finite-domain construction proves
both original base-field clauses: the real nonzero-challenge probability bound
and full finite-field saturation under polynomial field-size growth. Both
clauses keep their full list-decoding guarantees and use the same parameters.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Every finite binary additive domain has its literal power-of-two cardinality. -/
theorem allRate_domain_card_power {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) : ∃ d : ℕ, Nat.card D=2^d := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Fintype D := Fintype.ofFinite D
  refine ⟨Module.finrank (ZMod 2) D,?_⟩
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=D)
/-- The fixed dyadic parameters give the original uniform probability clause
and the full list-decoding consequence on every prescribed binary domain. -/
theorem all_rate_base_probability (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ) (hs : 2≤s)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ N0 : ℕ, ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
      (D : AddSubgroup F), N0≤(additiveDomain D).card →
      let S := additiveDomain D
      let N := S.card
      let J := ⌊ρ*N⌋₊
      let T := ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊
      ∃ f g : S → F, commonAgreementEQ S J f g J ∧
        (1/(1+(2:ℝ)^((ell+s)*s)*Fintype.card F/(N:ℝ)^s)-1/Fintype.card F)≤
          ((nonzeroBadChallenges S J f g T).card:ℝ)/Fintype.card F ∧
        ordinaryList S (J+1) T (badChallenges S J f g T).card := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_domain_pair_cutoff ρ hρ hρ' ell s hs hlow hroom
  refine ⟨2^d0,?_⟩
  intro F _ _ _ D hN
  obtain ⟨d,hD⟩ := allRate_domain_card_power D
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hd : d0≤d := by
    rw [hcard] at hN
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hN
  obtain ⟨f,g,hcommon,hbad,hlist⟩ := hcut d hd F D hD
  dsimp only
  simp only [hcard,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨f,g,hcommon,?_,hlist⟩
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
/-- For the same fixed dyadic parameters, every challenge is exceptional once
`s>2a` and the containing field has cardinality at most `N^a`. -/
theorem all_rate_base_saturation (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
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
      ∃ f g : S → F, commonAgreementEQ S J f g J ∧
        badChallenges S J f g T=Finset.univ ∧
        ordinaryList S (J+1) T (Fintype.card F) := by
  obtain ⟨d0,hd0,hcut⟩ := exists_all_rate_domain_pair_cutoff ρ hρ hρ' ell s hs hlow hroom
  obtain ⟨N1,hN11,hsat⟩ := allRate_eventual_pooling_ceil_eq_field_size a
    ((2:ℝ)^((ell+s)*s)) s (by positivity) has
  refine ⟨max (2^d0) N1,?_⟩
  intro F _ _ _ D hN hq
  obtain ⟨d,hD⟩ := allRate_domain_card_power D
  have hcard : (additiveDomain D).card=2^d := by rw [card_additiveDomain,hD]
  have hd : d0≤d := by
    have he : 2^d0≤2^d := by rw [←hcard]; exact (le_max_left _ _).trans hN
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp he
  obtain ⟨f,g,hcommon,hbad,hlist⟩ := hcut d hd F D hD
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
  refine ⟨f,g,hcommon,Finset.eq_univ_of_card _ hbadcard,?_⟩
  rwa [hbadcard] at hlist
end BinaryFieldCounterexamples
