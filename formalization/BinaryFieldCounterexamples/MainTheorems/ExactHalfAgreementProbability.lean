/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.ExactHalfAgreement
import Mathlib.Tactic.FieldSimp

/-!
# Main theorem companion: exact half-agreement probability

Theorem 4.7 and the opening paragraph of manuscript Section 4.3
(`sections/constructions/exact-half-agreement.tex`) identify the exceptional
probability as exactly `1 - 1/N` when the challenge field has size `2N`.
The full companion below retains all of the theorem's agreement and exceptional-set
clauses and adds the probability equality for the same fixed pair on the same affine domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Theorem 4.7's probability clause: a set of `2N-2` challenges in a field
of size `2N` has probability exactly `1-1/N`. Natural subtraction is justified
by the positive domain size. -/
theorem exact_half_probability_of_card (N b q : ℕ) (hN : 0 < N)
    (hb : b = 2 * N - 2) (hq : q = 2 * N) :
    (b : ℚ) / q = 1 - 1 / (N : ℚ) := by
  have hsub : 2 ≤ 2 * N := by omega
  have hNZ : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [hb, hq, Nat.cast_sub hsub]
  push_cast
  field_simp

/-- Theorem 4.7 in full, including the exact exceptional probability for
uniform challenges when `|F|=2N`. The probability is for the same pair that
satisfies every agreement bound and the exact exceptional-set description. -/
theorem exact_half_agreement_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F) (d : ℕ) (hd : 3 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hproper : 2 ^ d < Fintype.card F) :
    let E := affineDomain (additiveDomain D) a
    let N : ℕ := 2 ^ d
    let K : ℕ := N / 4
    ∃ f g : E → F,
      commonAgreementEQ E K f g K ∧ agreementEQ E K g K ∧
      agreementLE E K f (3 * N / 8 - 1) ∧
      (badChallenges E K f g (N / 2)).card = 2 * N - 2 ∧
      0 ∉ badChallenges E K f g (N / 2) ∧
      (Fintype.card F = 2 * N → ∃ s : F, s ≠ 0 ∧
        ∀ z : F, z ∈ badChallenges E K f g (N / 2) ↔ z ≠ 0 ∧ z ≠ s) ∧
      (Fintype.card F = 2 * N →
        ((badChallenges E K f g (N / 2)).card : ℚ) / Fintype.card F =
          1 - 1 / (N : ℚ)) := by
  obtain ⟨f, g, hcommon, hg, hf, hcount, hzero, hset⟩ :=
    exact_half_agreement D a d hd hD hproper
  refine ⟨f, g, hcommon, hg, hf, hcount, hzero, hset, ?_⟩
  intro hq
  exact exact_half_probability_of_card (2 ^ d) _ _ (by positivity) hcount hq

end BinaryFieldCounterexamples
