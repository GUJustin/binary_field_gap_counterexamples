/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import BinaryFieldCounterexamples.MainTheorems.TreeSupportAsymptotics
public import BinaryFieldCounterexamples.Constructions.Trees.DomainPair
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateCounts
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingCounts
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingDomainPair
public import BinaryFieldCounterexamples.Constructions.Trees.HalfRateProbability
public import BinaryFieldCounterexamples.Constructions.Trees.HalfAgreementAsymptotic

/-!
# Main theorem: Decision-tree counterexamples at rate one half

## Manuscript statement and status

Paper statement: [Theorem 6.10, p. 63](../../../binary-field-counterexamples.pdf#page=63).
Public theorem: `BinaryFieldCounterexamples.half_rate_decision_trees`.
**Proved.** The concrete theorem below covers all specified heights and the
height-two remark, using the exact constrained support count and padded locator
construction.

Let `D ⊆ F` be binary additive with `N = 2^d`, where `q = |F| > N`.
Choose `h ≥ 3` with `d ≥ 2^h - 1`, and put `K = N/2`, `w = N/2^(h+1)`.
Write `G(a,b) = [a choose b]_2`. Define `τ_j = 2^j - 1`, `δ_2 = 3`,
`δ_j = 2^(2 (2^(j-1) - 1)) δ_(j-1)^2`, and
`C_j = (∏ i = 0,...,τ_j-1, (2^τ_j - 2^i))/δ_j`.
The support counts are

`M_2(d) = 28 (6 · 2^(d-3) - 5)`,
`M_j(d) = (2^(j+1) - 1) M_(j-1)(d-1)
             · 2^(r_j²) G(d-1-r_j,r_j) C_(j-1)`, where `r_j = 2^(j-1)-1`.

Put `M = M_h(d)` and
`E = ((K - w - K²/(N-w)) M² + w M)/2`.
There is one pair with `agr_K(g) = CA_K(f,g) = K`, `agr_K(f) ≤ K + w - 1`,
and at least

`max { M - floor(E/(q-N)), ceil((q-N) M²/((q-N) M + 2 E)) }`

distinct nonzero exceptional challenges at agreement `K + w`. Here `E` denotes the
manuscript's collision bound `F`, renamed in prose to avoid confusion with the
field. Rational expressions and floors must not become truncated natural division.

For fixed height, `M_h(d) = Θ_h(N^(2^h-h-1))`, and uniformly over containing
challenge fields the exceptional probability is at least
`Ω_h(min {N^(2^h-h-1)/q, 1/N})`. The distinct count is of order `M_h(d)`
when `q ≥ N M_h(d)`. Heights `3,4,5` give agreement fractions
`9/16,17/32,33/64`, exponents `4,11,26`, and minimum dimensions `7,15,31`.
The common-agreement gap as a fraction is `2^(-h-1)`. The height-two remark
extends the finite and probability declarations to `h ≥ 2`.
-/

/-!
## Companion contract: half agreement on the whole domain

Paper statement: [Corollary 6.7, p. 61](../../../binary-field-counterexamples.pdf#page=61) in the same manuscript section.
Public theorem: `BinaryFieldCounterexamples.half_agreement_trees`.
**Proved.** Let `D ⊆ F` be binary additive with `N = 2^d` and
`q = |F| > N`. Choose `h ≥ 2` with `d ≥ τ_h = 2^h - 1`. This companion uses
different message length and support count from the half-rate theorem:

`T = N/2`, `K = N/2 - N/2^(h+1)`,
`M = B_h(d) = (∏ i = 0,...,τ_h-1, (2^d - 2^i))/δ_h`, and
`E = K · choose(M,2) - N · choose(M/2,2)`.

There is one pair with `CA_K(f,g) = agr_K(g) = K`, `agr_K(f) ≤ T - 1`, and
at least

`max {M - floor(E/(q-N)), ceil((q-N) M²/((q-N) M + 2 E))}`

distinct nonzero exceptional challenges at agreement `T`, with witnesses of degree
strictly below `K`. For fixed `h`, the count is
`Ω_h(min {N^(2^h-1), q/N})`. In particular `h = 2` gives rate `3/8`,
agreement `1/2`, and `Ω(min {N³,q/N})` challenges, hence a cubic count if `q ≥ N⁴`.

The proof uses all balanced height-`h` tree supports, without requiring avoidance
of a small subspace. Complementation gives incidence exactly `M/2` at every
coordinate, proving the displayed energy `E` by exterior incidence counting.
The support locators have form `P_A = X^T + J_A`, with `deg J_A ≤ K`.
Choose an exterior pole by collision pooling and apply normalized pole reduction:
the challenges are `P_A(β)`, nonzero because the locator roots lie in `D`.
The quotient witnesses agree exactly on their supports. Keep this support family,
collision formula, and `h ≥ 2` guard separate from the main `h ≥ 3` construction.
-/

/-!
## Proof assembly: 1. Count supports without counting representations twice

Prove the balanced-tree support recursion, the translation-period dimension,
and recovery of the branching functional and children. These establish that
`C_j` and `M_j` count distinct functions/supports. Count supports avoiding the
chosen small subspace, keeping that constraint through the recursion.
-/

/-!
## Proof assembly: 2. Construct locators and bound unordered collisions

Turn each union of disjoint flats into its locator polynomial, preserve common
high coefficients, and apply pole reduction with degree strictly below `K`.
Use the support-incidence calculation to prove the bound `E`. Track unordered
pairs consistently: the second-moment denominator contains `2 E`.
-/

/-!
## Proof assembly: 3. Take the stronger image bound and derive asymptotics

Apply both additive and second-moment collision bounds and take their maximum.
Establish that the counted challenges are nonzero, rather than subtracting a challenge
without matching the stated finite formula. Prove exact common agreement using
the shared agreement API and interpolation, then solve the fixed-height exponent
recurrence and convert the finite count to the uniform probability lower bound.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open scoped BigOperators

/-- Theorem 6.10: the finite count at every admitted height, with the rational
collision energy, both image-size bounds, and both individual agreement
guarantees preserved exactly. The height-two remark is also included. -/
theorem half_rate_decision_trees
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (d h : ℕ) (hh : 2 ≤ h) (hd : 2 ^ h - 1 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let K : ℕ := N / 2
    let w : ℕ := N / 2 ^ (h + 1)
    let M : ℕ := avoidingTreeSupportCount h d
    let q : ℕ := Fintype.card F
    let E : ℚ := (((K : ℚ) - w - (K : ℚ) ^ 2 / (N - w)) * M ^ 2 + w * M) / 2
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (K + w - 1) ∧
      max (M - ⌊E / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤
        (nonzeroBadChallenges A K f g (K + w)).card := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Fintype D := Fintype.ofFinite D
  have hDN : Nat.card D = 2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D = d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card, ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm
  have hheight : h+2 ≤ 2^h := by
    suffices ∀ j : ℕ, 2 ≤ j → j+2 ≤ 2^j from this h (by omega)
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ h hh ih => rw [pow_succ]; omega
  apply half_rate_trees_of_population D d h (by omega) (by omega) hD hq
  intro W hW
  have hp := Trees.avoidingTreeSupportFamily_card_eq (h-2) W
    (by simpa only [show h-2+2=h by omega, hdim] using hd)
    (by rw [hdim]; omega)
  simpa only [show h-2+2=h by omega, hdim] using hp

/-- Corollary 6.7: the whole-domain family has half agreement and its own
message length, individual bounds, and exact incidence collision energy. -/
theorem half_agreement_trees
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (d h : ℕ) (hh : 2 ≤ h) (hd : 2 ^ h - 1 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let T : ℕ := N / 2
    let K : ℕ := N / 2 - N / 2 ^ (h + 1)
    let M : ℕ := treeSupportCount h d
    let q : ℕ := Fintype.card F
    let E : ℚ := (K : ℚ) * Nat.choose M 2 - (N : ℚ) * Nat.choose (M / 2) 2
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T - 1) ∧
      max (M - ⌊E / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card := by
  exact half_agreement_trees_finite_count D d h hh hd hD hq

/-- Theorem 6.10, uniform probability consequence, with constants quantified
before the dimension, field, and prescribed domain. The same pair retains
both individual agreement guarantees from the finite theorem, including the
height-two remark. -/
theorem half_rate_decision_trees_probability (h : ℕ) (hh : 2 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ (d : ℕ), d₀ ≤ d → 2 ^ h - 1 ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
        (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let q : ℕ := Fintype.card F
        let K : ℕ := N / 2
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (K + N / 2 ^ (h + 1) - 1) ∧
          c * min ((N : ℝ) ^ (2 ^ h - h - 1) / q) (1 / N) ≤
            ((nonzeroBadChallenges A K f g (K + N / 2 ^ (h + 1))).card : ℝ) / q ∧
          (N * avoidingTreeSupportCount h d ≤ q →
            c * avoidingTreeSupportCount h d ≤
              ((nonzeroBadChallenges A K f g (K + N / 2 ^ (h + 1))).card : ℝ)) := by
  exact half_rate_decision_trees_probability_of_finite
    (fun D d h hh hd hD hq => half_rate_decision_trees D d h hh hd hD hq) h hh

/-- Corollary 6.7, fixed-height asymptotic count on every containing field.
The common and individual agreement guarantees still hold for the same pair. -/
theorem half_agreement_trees_asymptotic (h : ℕ) (hh : 2 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ (d : ℕ), d₀ ≤ d → 2 ^ h - 1 ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
        (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let K : ℕ := N / 2 - N / 2 ^ (h + 1)
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (N / 2 - 1) ∧
          c * min ((N : ℝ) ^ (2 ^ h - 1)) ((Fintype.card F : ℝ) / N) ≤
            ((nonzeroBadChallenges A K f g (N / 2)).card : ℝ) := by
  exact half_agreement_trees_asymptotic_proved h hh

end BinaryFieldCounterexamples
