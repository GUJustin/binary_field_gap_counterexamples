/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.ProperExtensionClause
public import BinaryFieldCounterexamples.Constructions.AllRates.HighExtensionClause

@[expose] public section

/-!
# Main theorem: Every fixed rate on every binary additive domain

## Manuscript statement and status

Paper statement: [Theorem 4.5, p. 33](../../../binary-field-counterexamples.pdf#page=33).
Public theorem: `BinaryFieldCounterexamples.all_rates_certain_failure`.
**Proved.** All four clauses below keep their original quantitative contracts,
with one choice of the agreement fraction and counting constant.

Fix a real `0 < ρ < 1` and an integer `s ≥ 2`. There are constants
`ρ < α_(ρ,s) < sqrt ρ` and `C_(ρ,s) > 0` such that, for every sufficiently
large binary additive domain `D ⊆ F` with `N = |D|`, `q = |F|`, and
`J = floor(ρ N)`, there is one pair with `CA_J(f,g) = J` and

`|Bad_(ceil(α_(ρ,s) N))(f,g) \ {0}|/q
  ≥ 1/(1 + C_(ρ,s) q/N^s) - 1/q`.

The cutoff and constants are uniform over `D` and its containing field.
For each fixed real `a ≥ 1`, choosing `s > 2 a` ensures that for every
sufficiently large such domain with `q ≤ N^a` there is a pair with
`CA_J(f,g) = J` and `Bad_(ceil(α_(ρ,s) N))(f,g) = F`, including zero.
At message length `J + 1`, the construction also yields a received word whose
decoding list has at least as many codewords at that threshold.

If `D ⊆ B ⊊ F`, a separate pair at the same rate and threshold has
`agr_J(f) = agr_J(g) = CA_J(f,g) = J` and nonzero exceptional count at least
`|B|/(1 + C_(ρ,s) |B|/N^s) - 1`. If `[F:B] ≥ s + 1`, the original
`q`-dependent lower bound can also be attained with both individual agreements
equal to `J`. These are different field hypotheses and may use different pairs.

The threshold stays strictly between rate and Johnson asymptotically, but is
not asserted to approach Johnson. Strict code degree is `< J`, or `< J + 1`
for the list-decoding consequence. Agreement will use the shared ArkLib API.
-/

/-!
## Proof assembly: 1. Cancel locator coefficients on a small subspace

For codimension-`s` subspaces, recursively cancel the highest coefficients of
their linearized locators. Divide the residual by `X` only after proving its
constant term vanishes, and keep a strict witness-degree bound.
Recover locator coefficients from the affine functions giving the challenges to prove those
functions are distinct. Their evaluations need not be injective for every choice.
-/

/-!
## Proof assembly: 2. Pool collisions and pad to the requested rate

Apply the generic collision-pooling lemma, select a sufficiently small fixed
dyadic subdomain fraction, and add common agreement coordinates outside it.
Track floor/ceiling errors in `J` and the final threshold with an explicit large
enough cutoff. The same parameter choice must supply one fixed pair and all
counted challenge witnesses. Prove common agreement equality, not merely a bound.
-/

/-!
## Proof assembly: 3. Prove the stronger finite-field saturation claim

The assertion that every challenge is exceptional requires the manuscript's
additional counting argument and `s > 2 a`; it does not follow by rounding an
unspecified asymptotic probability bound. Account explicitly for zero.
Then prove the list-decoding transfer at message length `J + 1` and the extension-coordinate
normalizations for the two both-far variants, keeping their distinct quantifiers.
-/

namespace BinaryFieldCounterexamples

open Polynomial

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Uniform arbitrary-domain theorem, including saturation, decoding lists,
and both distinct extension-field normalizations. The same `α,C` work throughout;
only the cutoff for saturation additionally depends on `a`. -/
theorem all_rates_certain_failure (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
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
  obtain ⟨ell,hlam,hlow,hroom,halpha,hJohnson⟩ :=
    exists_all_rate_dyadic_fraction ρ hρ hρ' s
  let α : ℝ := ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))
  let C : ℝ := (2:ℝ)^((ell+s)*s)
  obtain ⟨N0,hbase⟩ := all_rate_base_probability ρ hρ hρ' ell s hs hlow hroom
  obtain ⟨N2,hhigh⟩ := all_rate_high_extension ρ hρ hρ' ell s hs hlow hroom
  have hproper := all_rate_proper_extension_of_base_clause ρ α C s N0
    (fun B _ _ _ D hD => by
      obtain ⟨f,g,hcommon,hprob,hlist⟩ := hbase B D hD
      exact ⟨f,g,hcommon,hprob⟩)
  refine ⟨α,C,halpha,hJohnson,by dsimp [C]; positivity,max N0 N2,?_,?_,?_,?_⟩
  · intro F _ _ _ _ D hD
    exact hbase F D ((le_max_left N0 N2).trans hD)
  · intro a ha has
    obtain ⟨N1,hsat⟩ := all_rate_base_saturation ρ hρ hρ' ell s hs hlow hroom a has
    refine ⟨N1,?_⟩
    intro F _ _ _ _ D hD hq
    exact hsat F D hD hq
  · intro B F _ _ _ _ _ _ _ φ D hD hsize
    exact hproper B F φ D ((le_max_left N0 N2).trans hD) hsize
  · intro B F _ _ _ _ _ _ _ φ D hD hsize
    exact hhigh B F φ D ((le_max_right N0 N2).trans hD) hsize
end BinaryFieldCounterexamples
