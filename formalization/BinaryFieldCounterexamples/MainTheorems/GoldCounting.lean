/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.MomentPopulation
public import BinaryFieldCounterexamples.Constructions.Gold.BoundedAssembly

/-!
# Main theorem: The Gold counting bound near Johnson

## Manuscript statement and status

Paper statement: [Theorem 5.1, p. 36](../../../binary-field-counterexamples.pdf#page=36).
Public theorem: `BinaryFieldCounterexamples.gold_counting_sharp`.
The original `gold_counting` remains as a weaker compatibility corollary.
**Proved.** Both concrete conclusions use the shared polynomial agreement
semantics and follow from the actual moment kernel, finite Fourier population
bound, distinct locator family, and exact collision pooling. No external
rank-distribution theorem is assumed.

Let `B = GF(2^m)` and let `D ≤ B` be a binary additive subspace of dimension
`d`, with `N = 2^d`. Choose `2 ≤ t ≤ floor(d/2)`. Set `ι = 1` when `d`
is even and `ι = 0` otherwise, and assume `Δ = m - t (m - d + ι) ≥ 1`.
Define, with Gaussian binomial coefficients,

`L = 2^(2 t) (2^Δ - 1) [floor(d/2) choose t]_4`,
`T = N/2 - N/2^(t+1)`, and `δ = N/2^(2 t)`.

There is a word over `B` with at least `L` distinct degree-`< N/4` explaining
polynomials agreeing on at least `T` coordinates. For every finite extension
`F/B` of cardinality `q > N`, there is one pair over `F` with

* `agr_(N/4)(g) = CA_(N/4)(f,g) = N/4`;
* `agr_(N/4)(f) ≤ 3 N/8 - 1`; and
* at least the maximum of `L - floor(δ choose(L,2)/(q-N))` and
  `ceil(L (q-N)/(q-N+δ (L-1)))` distinct **nonzero** exceptional challenges
  at agreement `T`. Both bounds hold for the same pair.

The pair witnesses have degree at most `T/2 - 1`, hence strictly below `N/4`.
All conclusions also hold on each affine translate of `D`. Decoding lists
use alphabet `B`; the pair and its challenges use `F`.

The agreement notation is that of Section 3, Notation and common tools. The Lean
statement uses the shared ArkLib-backed agreement API, with decoding lists and
the image of the challenge map kept as separate finite sets. Integer
divisibility and positivity must precede natural-number divisions/subtractions.
-/

/-!
## Proof assembly: 1. Count the moment-constrained forms

Formalize Gold moment constraints and the rank/radical counts on the prescribed
subspace, including the parity correction `ι`. Prove the Gaussian count with
its actual parameter hypotheses. The key count is on this fixed domain; replacing
it by a convenient full field would lose the prescribed-domain conclusion.
-/

/-!
## Proof assembly: 2. Build distinct locators with common high coefficients

Use [Lemma 5.12, p. 43](../../../binary-field-counterexamples.pdf#page=43) to obtain many roots and common high coefficients.
Prove degree and coefficient recovery before deducing distinct codewords in the decoding list.
Preserve the stronger witness bound `T/2 - 1`, needed by later padding.
Canonical representatives over `B` must remain the specified polynomials when
evaluated at exterior poles; reduction modulo `X^|B| - X` is not harmless there.
-/

/-!
## Proof assembly: 3. Pool collisions and apply Lemma 3.13 to the inputs

Apply the pole reduction and both simultaneous collision bounds of [Lemma 3.19, p. 27](../../../binary-field-counterexamples.pdf#page=27)
over the `q - N` exterior poles. Convert the image cardinality into distinct
challenges. The bound on the first input of Lemma 3.13 is strictly below `T`, so none
of these challenges is zero and the full image count is kept.
Use the second input's agreement plus interpolation for the exact common agreement,
and [Lemma 3.13, p. 24](../../../binary-field-counterexamples.pdf#page=24) for the first-input bound. Finally transport the
entire construction along translation, including degrees and distinct challenges.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open scoped BigOperators

/-- Theorem 5.1, decoding-list conclusion over the base field. The explaining
polynomials have degree at most `T / 2`, hence strictly below `N / 4`.
The stricter `T / 2` dimension belongs only to the divided-difference pair witnesses. -/
theorem gold_counting_list
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (a : B) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0)) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let E := affineDomain (additiveDomain D) a
    ordinaryList E (N / 4) T L := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  dsimp only

  -- Count the actual moment-constrained tensors on this prescribed domain.
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  obtain ⟨e⟩ := Gold.exists_gold_basis D d hDN
  have hdt : 2*t≤d := by omega
  have hpopulation := Gold.card_momentTensors_lower_bound D m d t hB hDN e
    (by omega) hdt hΔ

  -- The fixed affine received word has all the distinct strict-degree explaining polynomials.
  obtain ⟨w,ps,hcard,hps⟩ := Gold.ordinaryList_from_basis_momentTensors D a d t hDN e ht hdt
  refine ⟨w,ps,?_,hps⟩
  apply le_trans ?_ hcard
  calc
    _ = ((2^(m-t*(m-d+if Even d then 1 else 0))-1)*gaussianBinomial 4 (d/2) t)*2^(2*t) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hpopulation


/-- The strengthened finite Gold theorem: both simultaneous collision bounds, no zero-challenge loss, and the same strict half-threshold witnesses. -/
theorem gold_counting_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) (a : B) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0))
    (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let δ : ℕ := N / 2 ^ (2 * t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := max (L-(δ*L.choose 2)/(q-N)) ⌈(L : ℚ) * ((q : ℚ) - (N : ℚ)) /
      ((q : ℚ) - (N : ℚ) + (δ : ℚ) * ((L : ℚ) - 1))⌉₊
    ∃ f g : E → F,
      commonAgreementEQ E (N / 4) f g (N / 4) ∧
      agreementEQ E (N / 4) g (N / 4) ∧
      agreementLE E (N / 4) f (3 * N / 8 - 1) ∧
      Z ≤ (nonzeroBadChallenges E (N / 4) f g T).card ∧
      Z ≤ (nonzeroBadChallenges E (T / 2) f g T).card := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  dsimp only

  -- The Fourier population bound and actual kernel dimension give the exact count.
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  obtain ⟨e⟩ := Gold.exists_gold_basis D d hDN
  have hdt : 2*t≤d := by omega
  have hpopulation := Gold.card_momentTensors_lower_bound D m d t hB hDN e
    (by omega) hdt hΔ
  have hL : 2^(2*t)*(2^(m-t*(m-d+if Even d then 1 else 0))-1)*gaussianBinomial 4 (d/2) t ≤
      (Gold.momentTensors D (Gold.basisParameter D e) t).card*2^(2*t) := by
    calc
      _ = ((2^(m-t*(m-d+if Even d then 1 else 0))-1)*gaussianBinomial 4 (d/2) t)*2^(2*t) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hpopulation

  -- Select exactly that many locators before pooling, preserving the precise denominator.
  -- One pair supplies the common/individual bounds and both strict witness dimensions.
  exact (Gold.gold_counting_from_tensor_lower_bound_sharp φ D a d t hDN e ht hdt hq _ hL).2

/-- A weaker compatibility form of Theorem 5.1, received-pair conclusion over every containing field with an
exterior point. The same pair supplies the stronger witness-degree count. -/
theorem gold_counting
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) (a : B) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0))
    (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let δ : ℕ := N / 2 ^ (2 * t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := ⌈(L : ℚ) * ((q : ℚ) - (N : ℚ)) /
      ((q : ℚ) - (N : ℚ) + (δ : ℚ) * ((L : ℚ) - 1))⌉₊ - 1
    ∃ f g : E → F,
      commonAgreementEQ E (N / 4) f g (N / 4) ∧
      agreementEQ E (N / 4) g (N / 4) ∧
      agreementLE E (N / 4) f (3 * N / 8 - 1) ∧
      Z ≤ (nonzeroBadChallenges E (N / 4) f g T).card ∧
      Z ≤ (nonzeroBadChallenges E (T / 2) f g T).card := by
  obtain ⟨f,g,hcommon,hg,hf,hbad,hstrong⟩ :=
    gold_counting_sharp φ D a m d t hB hD ht htd hΔ hq
  exact ⟨f,g,hcommon,hg,hf,
    (Nat.sub_le _ _).trans ((le_max_right _ _).trans hbad),
    (Nat.sub_le _ _).trans ((le_max_right _ _).trans hstrong)⟩

end BinaryFieldCounterexamples
