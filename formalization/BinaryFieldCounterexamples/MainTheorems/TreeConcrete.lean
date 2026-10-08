/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.HalfRateDecisionTrees
public import BinaryFieldCounterexamples.Constructions.Trees.ConcreteCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Main theorem specializations: concrete LeanVM and Flock tree bounds

Paper correspondence: Section 6.4, “Concrete bounds for the parameters of
LeanVM and Flock”, following [Theorem 6.10, p. 63](../../../binary-field-counterexamples.pdf#page=63).
All declarations below are proved. They quantify over every binary additive
domain of length `2^22` in the indicated challenge field, as the manuscript
requires. The words take values in that challenge field.

At height three and field size `2^192`, one fixed pair has common agreement
and second-input agreement `2^21`, first-input agreement at most `2359295`,
and at least `2030934687750743930807500565` distinct nonzero bad challenges
at agreement `9/16`. This exceeds `2.0309 × 10^27` and yields probability
strictly greater than `2^(-101.286)`. At height four the agreement is `17/32`
and the gap is `1/32`: over the 192-bit field the exact bound exceeds `2^172`,
and over the 256-bit field it exceeds `2^229`. The respective probability
bounds are at least `2^-20` and strictly greater than `2^-27`.

The concrete incidence energy is the exact rational expression of Theorem
6.10. Its integer evaluations are proved in `Trees.ConcreteCertificate`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- The dimension-22 specialization of Theorem 6.10, retaining the exact
collision bound and both individual agreement guarantees. -/
theorem tree_concrete_finite
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (h bits : ℕ)
    (hh : 3 ≤ h) (hd : 2^h-1 ≤ 22)
    (hD : (additiveDomain D).card = 2^22)
    (hq : Fintype.card F = 2^bits) (hb : 22 < bits) :
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A (2^21) f g (2^21) ∧
      agreementEQ A (2^21) g (2^21) ∧
      agreementLE A (2^21) f (2^21 + 2^22/2^(h+1)-1) ∧
      Trees.concreteTreeCount h bits ≤
        (nonzeroBadChallenges A (2^21) f g (2^21 + 2^22/2^(h+1))).card := by
  have hq' : 2^22 < Fintype.card F := by
    rw [hq]
    exact Nat.pow_lt_pow_right (by decide) hb
  obtain ⟨f,g,hc,hg,hf,hn⟩ := half_rate_decision_trees D 22 h (by omega) hd hD hq'
  refine ⟨f,g,?_,?_,?_,?_⟩
  · simpa only [show 2^22/2=2^21 by norm_num] using hc
  · simpa only [show 2^22/2=2^21 by norm_num] using hg
  · simpa only [show 2^22/2=2^21 by norm_num] using hf
  · simpa [Trees.concreteTreeCount, Trees.concreteTreeEnergy, hq,
      show 2^22/2=2^21 by norm_num, show (2:ℚ)^22=4194304 by norm_num] using hn

/-- LeanVM height three: the same pair realizes the exact count, conservative
decimal count and strict probability bound. Rate, agreement and common gap
are identified as fractions of the actual domain cardinality. -/
theorem leanVM_tree_height_three
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (hD : (additiveDomain D).card = 2^22)
    (hq : Fintype.card F = 2^192) :
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A 2097152 f g 2097152 ∧
      agreementEQ A 2097152 g 2097152 ∧
      agreementLE A 2097152 f 2359295 ∧
      2030934687750743930807500565 ≤
        (nonzeroBadChallenges A 2097152 f g 2359296).card ∧
      20309*10^23 < (nonzeroBadChallenges A 2097152 f g 2359296).card ∧
      Real.rpow 2 (-(101286/1000:ℝ)) <
        ((nonzeroBadChallenges A 2097152 f g 2359296).card:ℝ)/(Fintype.card F:ℝ) ∧
      (2097152:ℚ)/A.card = 1/2 ∧
      (2359296:ℚ)/A.card = 9/16 ∧
      (2359296-2097152:ℚ)/A.card = 1/16 := by
  obtain ⟨f,g,hc,hg,hf,hn⟩ := tree_concrete_finite D 3 192 (by decide) (by decide)
    hD hq (by decide)
  norm_num only [Trees.concreteTreeCount_three_192, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceSub] at hc hg hf hn
  refine ⟨f,g,hc,hg,hf,hn,?_,?_,?_,?_,?_⟩
  · exact (by norm_num : 20309*10^23 < 2030934687750743930807500565).trans_le hn
  · apply Trees.concreteTree_probability_lower.trans_le
    rw [hq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (by norm_num : 20309*10^23 ≤ 2030934687750743930807500565).trans hn
  all_goals norm_num [hD]

/-- LeanVM height four: the exact finite bound exceeds `2^172`, and the
exceptional probability is at least `2^-20` for this same received pair. -/
theorem leanVM_tree_height_four
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (hD : (additiveDomain D).card = 2^22)
    (hq : Fintype.card F = 2^192) :
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A 2097152 f g 2097152 ∧
      agreementEQ A 2097152 g 2097152 ∧
      agreementLE A 2097152 f 2228223 ∧
      7103373469922630731168802544744297143231762030400873 ≤
        (nonzeroBadChallenges A 2097152 f g 2228224).card ∧
      2^172 < (nonzeroBadChallenges A 2097152 f g 2228224).card ∧
      Real.rpow 2 (-20:ℝ) ≤
        ((nonzeroBadChallenges A 2097152 f g 2228224).card:ℝ)/(Fintype.card F:ℝ) ∧
      (2097152:ℚ)/A.card = 1/2 ∧
      (2228224:ℚ)/A.card = 17/32 ∧
      (2228224-2097152:ℚ)/A.card = 1/32 := by
  obtain ⟨f,g,hc,hg,hf,hn⟩ := tree_concrete_finite D 4 192 (by decide) (by decide)
    hD hq (by decide)
  norm_num only [Trees.concreteTreeCount_four_192, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceSub] at hc hg hf hn
  have hl : 2^172 < (nonzeroBadChallenges (additiveDomain D) 2097152 f g 2228224).card :=
    (by norm_num : 2^172 < 7103373469922630731168802544744297143231762030400873).trans_le hn
  refine ⟨f,g,hc,hg,hf,hn,hl,?_,?_,?_,?_⟩
  · rw [hq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    change (2:ℝ)^(-20:ℝ) ≤ _
    rw [Real.rpow_neg (by norm_num)]
    have hr : (2:ℝ)^(20:ℝ) = (2:ℝ)^20 := Real.rpow_natCast _ 20
    rw [hr]
    have hc' : (2:ℝ)^172 ≤
        ((nonzeroBadChallenges (additiveDomain D) 2097152 f g 2228224).card:ℝ) := by
      exact_mod_cast hl.le
    have hi : ((2:ℝ)^20)⁻¹ = (2:ℝ)^172/(2:ℝ)^192 := by norm_num
    rw [hi]
    exact div_le_div_of_nonneg_right hc' (by positivity)
  all_goals norm_num [hD]

/-- Flock height four: the exact finite bound exceeds `2^229`, giving strict
probability greater than `2^-27` while retaining agreement `17/32` and gap
`1/32` for the same received pair. -/
theorem flock_tree_height_four
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (hD : (additiveDomain D).card = 2^22)
    (hq : Fintype.card F = 2^256) :
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A 2097152 f g 2097152 ∧
      agreementEQ A 2097152 g 2097152 ∧
      agreementLE A 2097152 f 2228223 ∧
      1203738153600450193532348559198379334481679302144198224930361796779254 ≤
        (nonzeroBadChallenges A 2097152 f g 2228224).card ∧
      2^229 < (nonzeroBadChallenges A 2097152 f g 2228224).card ∧
      Real.rpow 2 (-27:ℝ) <
        ((nonzeroBadChallenges A 2097152 f g 2228224).card:ℝ)/(Fintype.card F:ℝ) ∧
      (2097152:ℚ)/A.card = 1/2 ∧
      (2228224:ℚ)/A.card = 17/32 ∧
      (2228224-2097152:ℚ)/A.card = 1/32 := by
  obtain ⟨f,g,hc,hg,hf,hn⟩ := tree_concrete_finite D 4 256 (by decide) (by decide)
    hD hq (by decide)
  norm_num only [Trees.concreteTreeCount_four_256, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceSub] at hc hg hf hn
  have hl : 2^229 < (nonzeroBadChallenges (additiveDomain D) 2097152 f g 2228224).card :=
    (by norm_num : 2^229 < 1203738153600450193532348559198379334481679302144198224930361796779254).trans_le hn
  refine ⟨f,g,hc,hg,hf,hn,hl,?_,?_,?_,?_⟩
  · rw [hq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    change (2:ℝ)^(-27:ℝ) < _
    rw [Real.rpow_neg (by norm_num)]
    have hr : (2:ℝ)^(27:ℝ) = (2:ℝ)^27 := Real.rpow_natCast _ 27
    rw [hr]
    have hc' : (2:ℝ)^229 <
        ((nonzeroBadChallenges (additiveDomain D) 2097152 f g 2228224).card:ℝ) := by
      exact_mod_cast hl
    have hi : ((2:ℝ)^27)⁻¹ = (2:ℝ)^229/(2:ℝ)^256 := by norm_num
    rw [hi]
    exact div_lt_div_of_pos_right hc' (by positivity)
  all_goals norm_num [hD]

end BinaryFieldCounterexamples
