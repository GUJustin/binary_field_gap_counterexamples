/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.AllRatesCertainFailure
public import BinaryFieldCounterexamples.Counting.CollisionSimplifiedBound

@[expose] public section

/-!
# Main theorem: Half-minimum counts at every fixed rate

Paper statement: [Theorem 4.5, p. 31](../../../binary-field-counterexamples.pdf#page=31).
Public theorem: `BinaryFieldCounterexamples.all_rates_certain_failure_half_min`.
**Proved.** This companion retains all four clauses of `all_rates_certain_failure`
with the same constants and cutoff, adding the two distinct nonzero challenge
counts printed after the probability bound in part 1.

For every `0 < ρ < 1` and integer `s ≥ 2`, choose `ρ < α < sqrt ρ` and `c > 0`.
Lean writes `C = 1/c`. On every sufficiently large binary additive domain of
size `N` in a field of size `q`, one pair at strict degree `< J = floor(ρ N)`
has common agreement `J` and, at threshold `T = ceil(α N)`, at least
`q/(1+q/(c N^s))-1 ≥ ½ min {q,c N^s}-1` nonzero exceptional challenges.
The probability and decoding-list conclusions hold for this same pair.

The saturation and two extension-field clauses are inherited unchanged, with
one choice of `α,c` for all four regimes. The proof multiplies the probability
bound by the positive field size and applies the elementary harmonic estimate;
it does not change the construction or its quantifier order.
-/

namespace BinaryFieldCounterexamples

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4.5 with both explicit count bounds in part 1. The same `α,C,N₀`
serve the probability, count, list, and extension conclusions. -/
theorem all_rates_certain_failure_half_min (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ α C : ℝ, ρ < α ∧ α < Real.sqrt ρ ∧ 0 < C ∧ ∃ N₀ : ℕ,
    (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
      (D : AddSubgroup F), N₀ ≤ (additiveDomain D).card →
      let S := additiveDomain D
      let N : ℕ := S.card
      let J : ℕ := ⌊ρ * N⌋₊
      let T : ℕ := ⌈α * N⌉₊
      ∃ f g : S → F,
        commonAgreementEQ S J f g J ∧
        (1 / (1 + C * Fintype.card F / (N : ℝ) ^ s) - 1 / Fintype.card F) ≤
          ((nonzeroBadChallenges S J f g T).card : ℝ) / Fintype.card F ∧
        (Fintype.card F : ℝ) / (1 + C * Fintype.card F / (N : ℝ) ^ s) - 1 ≤
          (nonzeroBadChallenges S J f g T).card ∧
        (1 / 2 : ℝ) * min (Fintype.card F : ℝ) ((N : ℝ) ^ s / C) - 1 ≤
          (nonzeroBadChallenges S J f g T).card ∧
        ordinaryList S (J + 1) T (badChallenges S J f g T).card) ∧
    (∀ a : ℝ, 1 ≤ a → (2 * a < s) → ∃ N₁ : ℕ,
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
        (D : AddSubgroup F), N₁ ≤ (additiveDomain D).card →
        (Fintype.card F : ℝ) ≤ ((additiveDomain D).card : ℝ) ^ a →
        let S := additiveDomain D
        let J : ℕ := ⌊ρ * S.card⌋₊
        let T : ℕ := ⌈α * S.card⌉₊
        ∃ f g : S → F, commonAgreementEQ S J f g J ∧
          badChallenges S J f g T = Finset.univ ∧
          ordinaryList S (J + 1) T (Fintype.card F)) ∧
    (∀ (B F : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2]
      [Field F] [Fintype F] [DecidableEq F] (φ : B →+* F)
      (D : AddSubgroup B), N₀ ≤ (additiveDomain D).card →
      Fintype.card B < Fintype.card F →
      let S := mappedDomain φ (additiveDomain D)
      let N : ℕ := S.card
      let J : ℕ := ⌊ρ * N⌋₊
      ∃ f g : S → F,
        agreementEQ S J f J ∧ agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
        (Fintype.card B : ℝ) / (1 + C * Fintype.card B / (N : ℝ) ^ s) - 1 ≤
          (nonzeroBadChallenges S J f g ⌈α * N⌉₊).card) ∧
    (∀ (B F : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2]
      [Field F] [Fintype F] [DecidableEq F] (φ : B →+* F)
      (D : AddSubgroup B), N₀ ≤ (additiveDomain D).card →
      Fintype.card B ^ (s + 1) ≤ Fintype.card F →
      let S := mappedDomain φ (additiveDomain D)
      let N : ℕ := S.card
      let J : ℕ := ⌊ρ * N⌋₊
      ∃ f g : S → F,
        agreementEQ S J f J ∧ agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
        (1 / (1 + C * Fintype.card F / (N : ℝ) ^ s) - 1 / Fintype.card F) ≤
          ((nonzeroBadChallenges S J f g ⌈α * N⌉₊).card : ℝ) / Fintype.card F) := by
  -- Keep the original uniform constants, cutoff, and all three other clauses.

  obtain ⟨α, C, hα, hJohnson, hC, N₀, hbase, hsat, hproper, hhigh⟩ :=
    all_rates_certain_failure ρ hρ hρ' s hs
  refine ⟨α, C, hα, hJohnson, hC, N₀, ?_, hsat, hproper, hhigh⟩
  intro F _ _ _ _ D hD
  obtain ⟨f, g, hcommon, hprob, hlist⟩ := hbase F D hD
  let S := additiveDomain D
  let N := S.card
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  have hN : (0 : ℝ) < N := by
    have hpos : 0 < N := Finset.card_pos.mpr ⟨0, by simp [S, additiveDomain]⟩
    exact_mod_cast hpos

  -- Convert probability to count before simplifying its two positive scales.

  have hcount : (Fintype.card F : ℝ) /
      (1 + C * Fintype.card F / (N : ℝ) ^ s) - 1 ≤
      (nonzeroBadChallenges S ⌊ρ * N⌋₊ f g ⌈α * N⌉₊).card := by
    have h := (le_div_iff₀ hq).mp hprob
    simpa only [sub_mul, one_div_mul_cancel (ne_of_gt hq), one_div_mul_eq_div] using h
  refine ⟨f, g, hcommon, hprob, hcount, ?_, hlist⟩
  have hhalf := half_min_le_div_one_add_div (Fintype.card F) ((N : ℝ) ^ s / C)
    hq (by positivity)
  have heq : (Fintype.card F : ℝ) / ((N : ℝ) ^ s / C) =
      C * Fintype.card F / (N : ℝ) ^ s := by
    field_simp
  rw [heq] at hhalf
  exact (sub_le_sub_right hhalf 1).trans hcount

end BinaryFieldCounterexamples
