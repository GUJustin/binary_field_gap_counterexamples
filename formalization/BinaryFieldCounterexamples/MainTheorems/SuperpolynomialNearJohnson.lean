/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.Constructions.Gold.FixedThresholdTheorem
public import BinaryFieldCounterexamples.Constructions.Gold.DenseAsymptoticTheorem

@[expose] public section

/-!
# Main theorem: Superpolynomial exceptional sets approaching Johnson

## Manuscript statements and status

Paper statements: [Corollary 5.2, p. 37](../../../binary-field-counterexamples.pdf#page=37) and its characteristic-separation consequence
[Theorem 5.4, p. 38](../../../binary-field-counterexamples.pdf#page=38).
Public theorem names: `BinaryFieldCounterexamples.superpolynomial_near_johnson` and
`BinaryFieldCounterexamples.no_fixed_polynomial_exceptional_bound`.
Both conclusions are proved from the finite Gold theorem.

## Two regimes and their quantifiers

Both conclusions supply one pair `f,g` fixed before the challenge `z`.
For an exceptional challenge, a polynomial `h_z` of degree strictly below `N/4` agrees
with `f + z*g` on the specified number of coordinates. The polynomial may
depend on `z`. Common agreement counts coordinates where two degree-`< N/4`
polynomials explain `f` and `g` simultaneously on the same set.

The first conclusion lets the agreement tend to `1/2` and gives a
superpolynomial exceptional count with a quasipolynomial challenge field.
The second fixes any agreement `a < 1/2` and defeats any proposed polynomial
count bound, with a polynomial challenge field whose exponent is chosen
*after* that bound. Do not combine the field-size claim of the second regime
with the exceptional-count claim of the first.

### Agreement approaching Johnson

Fix an integer `c ≥ 0`, put `θ = min {1/4, 1/(c+1)}`, and choose
`t = min {floor(d/4), floor((d+c-1)/(c+1))}`.
For every sufficiently large `d` and every binary additive `d`-space
`D ⊆ B = GF(2^(d+c))`, with `N = 2^d`, there exist quarter-rate decoding
lists over `B` and received pairs over some finite extension `F/B` such that

* `T/N = 1/2 - Θ_c(N^(-θ))`;
* the base-two logarithms of the list size and the number of distinct nonzero
  exceptional challenges are each at least `θ (1 - 2 θ) (log₂ N)² - O_c(log N)`;
* `CA_(N/4)(f,g) = N/4`;
* the nonzero exceptional probability is `Ω_c(N^(-1 + 2 θ))`; and
* `log₂ |F| = θ (1 - 2 θ) (log₂ N)² + O_c(log N)`.

The constants and cutoff are uniform over `D`. For `c ≤ 3`, the leading count
exponent is `1/8`, deficit order is `N^(-1/4)`, and probability lower-bound order
is `N^(-1/2)`. The decoding-list alphabet has size `2^c N`.

### No fixed polynomial exceptional bound

The separate characteristic-separation consequence says: for every real
`1/4 < a < 1/2`, `b > 0`, and `C₀ > 0`, arbitrarily large quarter-rate binary
codes on hyperplanes have polynomial-size challenge fields and one received
pair with `CA_(N/4) = N/4` and more than `C₀ N^b` exceptional challenges at
`ceil(a N)` agreements. These violate every proximity-loss allowance
`ε* < a - 1/4`. The compatibility endpoint in this file permits the polynomial
field-size exponent to depend on `a,b,C₀`. The stronger endpoint
`no_fixed_polynomial_exceptional_bound_optimal_exponent` in
`MainTheorems.OptimalFixedThreshold` chooses `floor(b)+1` before `a,C₀`,
and therefore proves the paper's assertion that the exponent depends only on `b`.

Explicitly, the quantifier order is
`∀ a,b,C₀, ∃ e, ∀ N₀, ∃ N ≥ N₀, ∃ B,D,F,f,g`.
The base field has size `2N`, the domain is a binary hyperplane in it, and
`|F| = (2N)^e`. There are more than `C₀ N^b` distinct challenges `z` for which
`∃ h_z` with the required degree and agreement. This does not assert a
superpolynomial count in a single family with a fixed polynomial field size.

For example, `a = 0.49`, `b = 2`, `C₀ = 1` can use `e = 4` and the finite
construction parameter `t = 6`. Agreement is `0.4921875`, the challenge field
has size `(2N)^4`, and the count is `Ω(N^3)`, eventually exceeding `N^2`.
Common agreement is exactly `N/4`. A proposed loss `ε* < 0.24` would demand
more than `N/4` common coordinates. Counts and probabilities remain distinct:
divide the count by the actual `|F|` to obtain the probability.
-/

/-!
## Proof assembly: 1. Discharge the finite Gold parameter guards

Apply `MainTheorems.GoldCounting` only after proving `t ≥ 2`, `t ≤ floor(d/2)`,
and `Δ ≥ 1`. Obtain `t = θ d + O_c(1)` and explicit Gaussian-product estimates.
Keep parity effects inside controlled errors, not inside an unstated restriction
to even lengths. Use the concrete agreement predicates in `PaperSemantics`, backed by ArkLib.
-/

/-!
## Proof assembly: 2. Choose an actual extension field

Put `Q = |B|` and `S = N + δ (L - 1)`. Choose `q` as the largest power of
`Q` not exceeding `S`, prove `q > S/Q` and eventually `q ≥ 2 N`, then apply
the finite collision-energy formula. The field cannot have an arbitrary real
cardinality. The loss of a factor of order `Q` must be included in the count.
-/

/-!
## Proof assembly: 3. Prove the fixed-threshold consequence separately

Choose integers `e > b + 1`, `t ≥ e` with `1/2 - 2^(-t-1) > a`.
Use hyperplanes in a field of size `2 N` and challenge size `(2 N)^e`.
Show the energy bound gives `Ω_(t,e)(N^(e-1))` distinct nonzero challenges and
that the agreement clears `ceil(a N)` for large `N`. This fixed-`t` argument
supplies polynomial challenge fields; the growing-`t` dense-domain statement
alone does not assert that field-size restriction.
-/

namespace BinaryFieldCounterexamples

open Polynomial

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Uniform quantified version of the dense Gold asymptotics. All constants are
chosen before the ambient field and prescribed domain. Exponentials express the
base-two logarithmic bounds without taking logarithms of zero. -/
theorem superpolynomial_near_johnson (c : ℕ) :
    let θ : ℝ := min (1 / 4) (1 / (c + 1))
    ∃ A C p : ℝ, 0 < A ∧ 0 < C ∧ 0 < p ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2 ^ (d + c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2 ^ d →
    let N : ℕ := 2 ^ d
    let E : ℝ := θ * (1 - 2 * θ) * (d : ℝ) ^ 2
    ∃ T L : ℕ,
      A * (N : ℝ) ^ (-θ) ≤ 1 / 2 - (T : ℝ) / N ∧
      1 / 2 - (T : ℝ) / N ≤ C * (N : ℝ) ^ (-θ) ∧
      (2 : ℝ) ^ (E - C * d) ≤ L ∧
      ordinaryList (additiveDomain D) (N / 4) T L ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (additiveDomain D)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N / 4) f g (N / 4) ∧
        (2 : ℝ) ^ (E - C * d) ≤
          (nonzeroBadChallenges D' (N / 4) f g T).card ∧
        p * (N : ℝ) ^ (-1 + 2 * θ) ≤
          ((nonzeroBadChallenges D' (N / 4) f g T).card : ℝ) / Fintype.card F ∧
        (2 : ℝ) ^ (E - C * d) ≤ Fintype.card F ∧
        (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (E + C * d) := by
  exact Gold.denseGold_asymptotic c

/-- No fixed polynomial exceptional-count bound below Johnson.

Given `1/4 < a < 1/2` and a proposed bound `C₀ N^b`, choose the field-size
exponent `e` once. For every lower size bound `N₀`, construct a domain of size
`N = 2^d ≥ N₀` in a base field of size `2N`, a containing challenge field of
size `(2N)^e`, and one pair with common agreement exactly `N/4`.
More than `C₀ N^b` challenges give combination agreement at least `ceil(aN)`.

The final existential `∃ f g` precedes the exceptional-set cardinality: one pair works
for all counted challenges. `badChallenges` uses actual polynomial evaluations,
with an existential explaining polynomial inside each challenge's membership
condition. The exponent is not required to be uniform in `a,b,C₀`.

The proof follows the fixed-parameter regime described above. -/
theorem no_fixed_polynomial_exceptional_bound
    (a b C₀ : ℝ) (ha : 1 / 4 < a) (ha' : a < 1 / 2)
    (hb : 0 < b) (hC₀ : 0 < C₀) :
    ∃ e : ℕ, ∀ N₀ : ℕ, ∃ d : ℕ, N₀ ≤ 2 ^ d ∧
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B = 2 ^ (d + 1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card = 2 ^ d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F = (2 ^ (d + 1)) ^ e ∧
    let D' := mappedDomain φ (additiveDomain D)
    let N : ℕ := 2 ^ d
    ∃ f g : D' → F,
      commonAgreementEQ D' (N / 4) f g (N / 4) ∧
      C₀ * (N : ℝ) ^ b <
        (badChallenges D' (N / 4) f g ⌈a * N⌉₊).card := by
  exact no_fixed_polynomial_exceptional_bound_construction a b C₀ ha ha' hb hC₀
end BinaryFieldCounterexamples
