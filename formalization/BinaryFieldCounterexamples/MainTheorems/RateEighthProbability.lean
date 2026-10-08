/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.RateEighthFinite
public import BinaryFieldCounterexamples.Constructions.RateEighth.Probability

/-!
# Main theorem: decimal probability at rate `1/8`

This proves the final numerical clause of
[Corollary 4.6, p. 34](../../../binary-field-counterexamples.pdf#page=34).
On every prescribed binary additive domain of size `2^20` in a field of size
`2^64`, and every translate of that domain, there is one fixed pair with
strict Reed–Solomon message bound `K = 2^17`, second-input and common agreement
exactly `K`, and at least `45812722234` distinct challenges giving agreement
`3*2^16`. Its exceptional count exceeds `4.58*10^10` and `2^(64-28.585)`, and
its exceptional probability under uniform sampling from the entire challenge
field exceeds `2^(-28.585)`. The count uses all challenges, without excluding zero.

The construction and exact ceiling are supplied by `rate_eighth_finite` and
`rate_eighth_finite_count`; the real-power comparison is transferred from a
kernel-checked integer certificate in `Constructions.RateEighth.Probability`.
All declarations are proved, with only Lean's standard axioms.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Corollary 4.6's finite example on every translate of a prescribed domain:
one actual fixed pair satisfies the exact count and both printed decimal bounds.
The denominator is the actual size of the challenge field, so the final ratio
is its exceptional probability under a uniform challenge. -/
theorem rate_eighth_finite_probability
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F)
    (hD : (additiveDomain D).card = 2^20) (hF : Fintype.card F = 2^64) :
    let E := affineDomain (additiveDomain D) a
    ∃ f g : E → F,
      commonAgreementEQ E (2^17) f g (2^17) ∧ agreementEQ E (2^17) g (2^17) ∧
      45812722234 ≤ (badChallenges E (2^17) f g (3*2^16)).card ∧
      (458*10^8 : ℝ) < ((badChallenges E (2^17) f g (3*2^16)).card : ℝ) ∧
      (2 : ℝ)^(64 - 28.585 : ℝ) <
        ((badChallenges E (2^17) f g (3*2^16)).card : ℝ) ∧
      (2 : ℝ)^(-28.585 : ℝ) <
        ((badChallenges E (2^17) f g (3*2^16)).card : ℝ)/(Fintype.card F : ℝ) := by
  classical

  -- Construct one fixed pair and evaluate its exact rational ceiling.
  have h := rate_eighth_finite D a (2^15) (by norm_num) ⟨15, rfl⟩
    (by simpa using hD)
  dsimp only at h
  rw [hF] at h
  have hc := rate_eighth_finite_count
  dsimp only at hc
  rw [hc] at h
  norm_num only [show 4*2^15 = 2^17 by norm_num,
    show 6*2^15 = 3*2^16 by norm_num] at h
  obtain ⟨f, g, hcommon, hg, hcount⟩ := h
  have hcast : (45812722234 : ℝ) ≤
      ((badChallenges _ (2^17) f g (3*2^16)).card : ℝ) := by
    exact_mod_cast hcount
  refine ⟨f, g, hcommon, hg, hcount, ?_, ?_, ?_⟩

  -- Transfer the integer lower bound through positive real powers and division.
  · exact lt_of_lt_of_le (by norm_num) hcast
  · exact RateEighth.count_real_lower.trans_le hcast
  · apply RateEighth.probability_real_lower.trans_le
    rw [hF]
    push_cast
    convert div_le_div_of_nonneg_right hcast
      (show (0 : ℝ) ≤ (2 : ℝ)^64 by positivity) using 1
    norm_num

end BinaryFieldCounterexamples
