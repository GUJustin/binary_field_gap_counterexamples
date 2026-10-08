/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.ProperExtensionClause
public import BinaryFieldCounterexamples.Constructions.AllRates.BaseClausesFull
public import BinaryFieldCounterexamples.Constructions.AllRates.HighExtensionClause

@[expose] public section

/-!
# Main theorem: Complete all-rate certain failure

This proved companion assembles every clause of Theorem 4.5, p. 33, including
exact agreement of the second input in parts 1–2 and the closing decoding list
for the actual first input. One dyadic exponent, agreement fraction, and positive
counting constant work in all four field regimes. The exposed formula is
`α = ρ + 1 / 2^(ell+s+2)`, exactly the paper's `ρ + 2^(-r-s-2)`.

The code bounds remain strict: `< floor(ρ N)` for exceptional challenges and
`< floor(ρ N)+1` for the first-input decoding lists. The finite padding theorem
proves monicity and degree of the second input; root counting supplies its
upper agreement bound and simultaneous interpolation supplies attainment.
-/

namespace BinaryFieldCounterexamples

open Polynomial

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4.5 in full: all four clauses, exact second-input agreement in parts 1–2, first-input decoding lists, and the explicit dyadic agreement fraction from the following paragraph. -/
theorem all_rates_certain_failure_full (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ ell : ℕ, ∃ α C : ℝ, α = ρ + 1 / (2:ℝ)^(ell+s+2) ∧
      C = (2:ℝ)^((ell+s)*s) ∧
      ρ < α ∧ α < Real.sqrt ρ ∧ 0 < C ∧ ∃ N₀ : ℕ,
    (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
      (D : AddSubgroup F), N₀ ≤ (additiveDomain D).card →
      let S := additiveDomain D
      let N : ℕ := S.card
      let J : ℕ := ⌊ρ * N⌋₊
      let T : ℕ := ⌈α * N⌉₊
      ∃ f g : S → F,
        agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
        (1 / (1 + C * Fintype.card F / (N : ℝ) ^ s) - 1 / Fintype.card F) ≤
          ((nonzeroBadChallenges S J f g T).card : ℝ) / Fintype.card F ∧
        (∃ ps : Finset F[X], (badChallenges S J f g T).card = ps.card ∧
          ∀ p ∈ ps, p.degree < J+1 ∧ T ≤ agreementCount S f p)) ∧
    (∀ a : ℝ, 1 ≤ a → (2 * a < s) → ∃ N₁ : ℕ,
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
        (D : AddSubgroup F), N₁ ≤ (additiveDomain D).card →
        (Fintype.card F : ℝ) ≤ ((additiveDomain D).card : ℝ) ^ a →
        let S := additiveDomain D
        let J : ℕ := ⌊ρ * S.card⌋₊
        let T : ℕ := ⌈α * S.card⌉₊
        ∃ f g : S → F, agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
          badChallenges S J f g T = Finset.univ ∧
          (∃ ps : Finset F[X], Fintype.card F = ps.card ∧
            ∀ p ∈ ps, p.degree < J+1 ∧ T ≤ agreementCount S f p)) ∧
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
  -- Choose one dyadic fraction for every field and domain in the four clauses.

  obtain ⟨ell,hlam,hlow,hroom,halpha,hJohnson⟩ :=
    exists_all_rate_dyadic_fraction ρ hρ hρ' s
  let α : ℝ := ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))
  let C : ℝ := (2:ℝ)^((ell+s)*s)
  -- Assemble the complete base pair and each separate extension normalization.

  obtain ⟨N0,hbase⟩ := all_rate_base_probability_full ρ hρ hρ' ell s hs hlow hroom
  obtain ⟨N2,hhigh⟩ := all_rate_high_extension ρ hρ hρ' ell s hs hlow hroom
  have hproper := all_rate_proper_extension_of_base_clause ρ α C s N0
    (fun B _ _ _ D hD => by
      obtain ⟨f,g,hg,hcommon,hprob,hlist⟩ := hbase B D hD
      exact ⟨f,g,hcommon,hprob⟩)
  -- Expose the paper's threshold formula before collecting the uniform cutoffs.

  have hα : α = ρ + 1 / (2:ℝ)^(ell+s+2) := by
    dsimp [α]
    rw [show ell+s+2 = ell+(s+2) by omega, pow_add]
    congr 1
    field_simp
    simp [pow_add, mul_assoc]
  refine ⟨ell,α,C,hα,rfl,halpha,hJohnson,by dsimp [C]; positivity,max N0 N2,?_,?_,?_,?_⟩
  · intro F _ _ _ _ D hD
    exact hbase F D ((le_max_left N0 N2).trans hD)
  · intro a ha has
    obtain ⟨N1,hsat⟩ := all_rate_base_saturation_full ρ hρ hρ' ell s hs hlow hroom a has
    refine ⟨N1,?_⟩
    intro F _ _ _ _ D hD hq
    exact hsat F D hD hq
  · intro B F _ _ _ _ _ _ _ φ D hD hsize
    exact hproper B F φ D ((le_max_left N0 N2).trans hD) hsize
  · intro B F _ _ _ _ _ _ _ φ D hD hsize
    exact hhigh B F φ D ((le_max_right N0 N2).trans hD) hsize
end BinaryFieldCounterexamples
