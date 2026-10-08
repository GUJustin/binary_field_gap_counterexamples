/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.MainTheorems.DenseRateCoverage
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.PairAsymptotic
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.RateGap

@[expose] public section

/-!
# Main theorem: Superpolynomial counterexamples at every fixed rate on dense domains

## Manuscript statement and status

Paper statement: [Corollary 5.24, p. 56](../../../binary-field-counterexamples.pdf#page=56).
Intended theorem name: `BinaryFieldCounterexamples.dense_all_rates`.
**Proved.** The actual trace-form population, uniform affine restriction, balanced padding, and finite-extension pole construction establish the statement below.

Fix binary codimension `c ≥ 0`, put `a = 2^c`, and choose a fixed binary power
`b > a`. Let `B = GF(M)` where `M = b^(2 n)`, and let `D ⊆ B` be any affine
binary subspace of codimension `c`, of size `N = M/a`. Fix

`a/b² < ρ < 1 - a/b + a/b²`, `J = floor(ρ N)`, and
`α = 1/b + (ρ - a/b²)(1 - 1/b)`.

For all sufficiently large `n`, there is a word on `D` over `B` with
`N^(Ω_b(log N))` distinct degree-`< J` explaining polynomials at agreement fraction
at least `α - O_(b,c)(N^(-1/4))`. There is also one pair on `D` over an
extension `F/B` with `|F| = N^(O_(b,c)(log N))`,
`agr_J(f) = agr_J(g) = CA_J(f,g) = J`, and
`N^(Ω_b(log N))` distinct nonzero exceptional challenges at that agreement fraction.
These estimates are uniform over `D`; the decoding-list alphabet has size `a N`.

Moreover `ρ < α < sqrt ρ`. For every fixed `c` and `0 < ρ < 1`, a sufficiently
large fixed binary power `b` makes the rate interval applicable. The threshold
does not in general approach Johnson as `N` increases.

The Lean statement quantifies the size cutoff after the fixed rate
and field parameters, and uses integer thresholds for the fractional agreement
conclusion. Shared ArkLib agreement sets supply the ordinary/common semantics.
-/

/-!
## Proof assembly: 1. Restrict quadratic-form agreement sets uniformly

Start from the full-field theorem `MainTheorems.QuadraticForms` with
`t = floor(n/2)` and initial degree bound `K₀ = M/b²`.
For each nonzero scalar, show the binary trace form has the asserted rank and
that restriction to `D` loses at most `2 c` in rank. Character orthogonality
then leaves at least `N/b - O_(b,c)(N^(3/4))` roots on every prescribed `D`.
An average over domains would not establish this theorem.
-/

/-!
## Proof assembly: 2. Pad the unused degree and control the inputs' agreement

Use the available degree difference up to `J` to add agreement coordinates,
with a locator-padding argument and an explicit bound for the count lost.
Prove the normalized individual agreements and common agreement all equal `J`.
The both-far conclusion is stronger than the second-input bound alone.
-/

/-!
## Proof assembly: 3. Choose the extension and derive the rate interval

Preserve a superpolynomial number of distinct challenges through pole evaluation
and remove zero explicitly. Choose a genuine finite extension of `B` satisfying
the field-size estimate, then check both inequalities `ρ < α < sqrt ρ` using
the stated open rate interval. Do not identify this dense-domain result with
the arbitrary sparse-domain construction in `MainTheorems.AllRatesCertainFailure`.
-/

namespace BinaryFieldCounterexamples

open Polynomial

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Full dense-domain asymptotic contract, with a genuine finite extension,
both individual-agreement equalities, decoding lists, and constants uniform over affine
domains.
The cutoff may depend on the fixed rate. Proved. -/
theorem dense_all_rates (k : ℕ) (hk : 0 < k) :
    ∃ A : ℝ, 0 < A ∧ ∀ c : ℕ, c < k → ∃ C : ℝ, 0 < C ∧
    ∀ ρ : ℝ,
      (2 : ℝ) ^ c / ((2 : ℝ) ^ k) ^ 2 < ρ →
      ρ < 1 - (2 : ℝ) ^ c / (2 : ℝ) ^ k +
        (2 : ℝ) ^ c / ((2 : ℝ) ^ k) ^ 2 →
    let b : ℕ := 2 ^ k
    let α : ℝ := 1 / b + (ρ - (2 : ℝ) ^ c / (b : ℝ) ^ 2) * (1 - 1 / b)
    ρ < α ∧ α < Real.sqrt ρ ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = b ^ (2 * n) →
    ∀ (D : AddSubgroup B) (v : B),
    (additiveDomain D).card * 2 ^ c = Fintype.card B →
    let S := affineDomain (additiveDomain D) v
    let N : ℕ := S.card
    let J : ℕ := ⌊ρ * N⌋₊
    ∃ T L : ℕ,
      α - C * (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (T : ℝ) / N ∧
      (N : ℝ) ^ (A * Real.log N) ≤ L ∧ ordinaryList S J T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F,
    let S' := mappedDomain φ S
    ∃ f g : S' → F,
      agreementEQ S' J f J ∧ agreementEQ S' J g J ∧
      commonAgreementEQ S' J f g J ∧
      (N : ℝ) ^ (A * Real.log N) ≤ (nonzeroBadChallenges S' J f g T).card ∧
      (Fintype.card F : ℝ) ≤ (N : ℝ) ^ (C * Real.log N) := by
  obtain ⟨A,hA,h⟩ := DenseConstruction.dense_ordinary_and_pair_asymptotic k hk
  refine ⟨A,hA,?_⟩
  intro c hc
  obtain ⟨C,hC,hrest⟩ := h c hc
  refine ⟨C,hC,?_⟩
  intro ρ hlo hhi
  have hgap := dense_agreement_fraction_gap ((2:ℝ)^c) ((2:ℝ)^k) ρ
    (one_le_pow₀ (by norm_num)) (one_lt_pow₀ (by norm_num) (by omega)) hlo hhi
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgap.1
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgap.2
  · obtain ⟨n0,hn0⟩ := hrest ρ hlo hhi
    refine ⟨n0,?_⟩
    intro n hn B _ _ _ _ hB D v hD
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hn0 n hn B hB D v hD


end BinaryFieldCounterexamples
