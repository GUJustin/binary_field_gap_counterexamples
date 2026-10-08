/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianBinomial
public import BinaryFieldCounterexamples.Constructions.Gold.HalfRateConstruction
public import BinaryFieldCounterexamples.Constructions.Gold.NativeConstruction
public import BinaryFieldCounterexamples.Constructions.Gold.MomentPopulation

/-!
# Main theorem: The finite 128-bit challenge-field example

## Manuscript statement and status

Paper statement: [Corollary 5.18, p. 49](../../../binary-field-counterexamples.pdf#page=49).
Public theorem: `BinaryFieldCounterexamples.native128Example_sharp`.
The original `native128Example` remains a compatible weaker statement.
**Proved.** The concrete endpoint includes the exact numerical certificate.
It is a finite-field statement about a pair of words, not an implementation-security theorem.

Let `D` be any binary 27-dimensional subspace of `B = GF(2^32)`, or any affine
translate. Set `N = 2^27`, `K = 2^25`, and `F = GF(2^128)`, with a specified
embedding `B → F`. There is one pair `f,g : D → F` with

* `CA_K(f,g) = agr_K(g) = K`;
* `agr_K(f) ≤ 193 N/512 - 1`; and
* more than `3.4248 · 10^29` distinct nonzero exceptional challenges with
  agreement at least `T = 16193 N/32768`.

For uniform `z ∈ F`, the exceptional probability is greater than `2^(-29.889)`.
The input alphabet and challenge field are both `F`; `B` contains the domain.
All witnesses have polynomial degree strictly below `K`.

## Verified exact certificate

Use `d = 27`, `m = 32`, `t = 6`, `Δ = 2`, `δ = 2^15`, and `q = 2^128`.
Define

`L = 2^12 · 3 · [13 choose 6]_4`,
`Z = max(L - floor(δ choose(L,2)/(q-N)), ceil(L(q-N)/(q-N+δ(L-1))))`,
`p = paddingRetentionProbability 27 19 12`, and
`Bcount = ceil(p Z) = 342482627693920113354525730019`.

The exact proof establishes at least `Bcount` challenges, followed by the
two displayed conservative lower bounds. Gaussian products and ceilings must be
evaluated with exact integers/rationals; decimal approximations are not evidence.
The probability bound additionally requires a certified real-power inequality.
-/

/-!
## Companion contract: Gold families at rate one half

Paper statement: [Corollary 5.15, p. 46](../../../binary-field-counterexamples.pdf#page=46).
Public theorem: `BinaryFieldCounterexamples.gold_half_rate_sharp`.
The original `gold_half_rate` keeps its earlier conservative count.
**Proved.** Let `B = GF(2^m)` and `D ≤ B` be binary additive of
dimension `d`, with `N = 2^d`. Choose `2 ≤ t ≤ floor(d/2)`, put `ι = 1`
for even `d` and `0` for odd `d`, and assume `Δ = m - t(m-d+ι) ≥ 1`.
Let `F/B` be any finite extension with `q = |F| > N`. In addition to these
GoldCounting hypotheses, assume `2 t ≤ d - 2`. Set

`L = 2^(2 t) (2^Δ - 1) [floor(d/2) choose t]_4`,
`δ = N/2^(2 t)`,
`Z = max(L - floor(δ choose(L,2)/(q-N)), ceil(L(q-N)/(q-N+δ(L-1))))`,
`p = paddingRetentionProbability d (d-2) (2*t)`, and
`T_half = 5 N/8 - 3 N/2^(t+3)`.

On the same domain and over the same input/challenge field `F`, there is a
pair with `CA_(N/2)(f,g) = N/2` and at least `ceil(p Z)` distinct nonzero
exceptional challenges at agreement `T_half`, using polynomial witnesses of degree
strictly below `N/2`. The dense-domain quasipolynomial counts therefore persist
at rate one half, with agreement tending to `5/8` and common-agreement gap
tending to `1/8`. This companion does not assert the individual bounds
of the quarter-rate finite example without a further argument.

Proof plan: choose one Gold witness per retained nonzero challenge. Its agreement
set is invariant under the polar radical of dimension `d - 2 t`. Apply
[Lemma 5.14, p. 46](../../../binary-field-counterexamples.pdf#page=46) with initial degree bound `K₀ = N/4` and padding dimension
`w = d - 2`, hence padding size `N/4`. Use the exact retained fraction `p`, the
new strict degree bound, and `T + (N/4)(1-T/N) = T_half`, where
`T = N/2 - N/2^(t+1)`. For the dense-domain parameter choices, the original union bound still implies `p → 1`.
The extra guard `2 t ≤ d - 2` is essential to this padding application.
-/

/-!
## Proof assembly: 1. Specialize GoldCounting before padding

Obtain initial agreement `T₀ = 63 N/128` and strict witness degree below
`K₀ = N/4 - N/256`. Keep this stronger degree bound: the generic quarter-rate
conclusion alone leaves no demonstrated room for padding.
The quadratic polar radical has dimension `d - 2 t = 15`, which supplies the
translation invariance required by [Lemma 5.14, p. 46](../../../binary-field-counterexamples.pdf#page=46).
-/

/-!
## Proof assembly: 2. Apply exact locator padding

Use padding dimension `19`, size `w = 2^19 = N/256`, and the exact success probability `p`.
Check `K₀ + w = K` and `T₀ + w (1 - T₀/N) = 16193 N/32768`.
Use the first input of Lemma 3.13 before padding; its bound becomes
`3 N/8 + w/2 - 1 = 193 N/512 - 1`. The gap above this bound excludes zero, so no challenge is lost.
Prove both exact second-input/common agreement and
transport to affine translates using the shared ArkLib agreement interfaces.
-/

/-!
## Proof assembly: 3. Separate the finite theorem from system interpretation

Finish a small exact numerical certificate after the construction theorem exists.
A field/domain match with Binius64 does not establish that the pair is reachable
in a protocol execution. No oracle size, interleaving, or attack claim follows
from this theorem about a pair of words without additional hypotheses and a separate proof.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- A weaker compatibility form of Corollary 5.18, using the earlier collision
and union-bound retention estimates. The sharp endpoint below proves the paper's
larger retained count. This form retains both conservative numerical claims.
All numerical inequalities, including the real-power probability bound, are
proved from exact integer and rational certificates. -/
theorem native128Example
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hB : Fintype.card B = 2 ^ 32)
    (hF : Fintype.card F = 2 ^ 128)
    (D : AddSubgroup B) (a : B) (hD : (additiveDomain D).card = 2 ^ 27) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let N : ℕ := 2 ^ 27
    let K : ℕ := 2 ^ 25
    let q : ℕ := 2 ^ 128
    let L : ℕ := 2 ^ 12 * 3 * gaussianBinomial 4 13 6
    let Z := ⌈(L : ℚ) * (q - N) / (q - N + 2 ^ 15 * (L - 1))⌉₊ - 1
    let ε : ℚ := ((2 ^ 12 - 1) * (2 ^ 8 - 1)) / (2 ^ 27 - 1)
    let Bcount := ⌈(1 - ε) * Z⌉₊
    ∃ f g : E → F,
      commonAgreementEQ E K f g K ∧ agreementEQ E K g K ∧
      agreementLE E K f (193 * N / 512 - 1) ∧
      Bcount ≤ (nonzeroBadChallenges E K f g (16193 * N / 32768)).card ∧
      (34247 * 10 ^ 25 : ℕ) < Bcount ∧
      Real.rpow 2 (-(29889 / 1000 : ℝ)) <
        ((nonzeroBadChallenges E K f g (16193 * N / 32768)).card : ℝ) / q := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  have hDN : Nat.card D=2^27 := by rwa [card_additiveDomain] at hD
  obtain ⟨e⟩ := Gold.exists_gold_basis D 27 hDN
  have hpopulation := Gold.card_momentTensors_lower_bound D 32 27 6 hB hDN e
    (by decide) (by decide) (by norm_num [show ¬Even 27 by decide])
  have hL : Gold.nativeGoldListSize≤(Gold.momentTensors D (Gold.basisParameter D e) 6).card*2^12 := by
    have hp : 3*gaussianBinomial 4 13 6≤(Gold.momentTensors D (Gold.basisParameter D e) 6).card := by
      simpa only [show ¬Even 27 by decide,ite_false,Nat.reduceSub,Nat.reduceAdd,Nat.reduceMul,
        Nat.reducePow,Nat.reduceDiv] using hpopulation
    dsimp only [Gold.nativeGoldListSize]
    calc
      _ = (3*gaussianBinomial 4 13 6)*2^12 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := Gold.native_pair_from_tensor_lower_bound φ D a hDN e hF hL
  dsimp only
  refine ⟨f,g,hcommon,hg,hf,hbad,Gold.nativeGoldPaddedCount_certificate.1,?_⟩
  apply Gold.nativeGoldPaddedCount_certificate.2.trans_le
  rw [Nat.cast_pow,Nat.cast_ofNat]
  apply div_le_div_of_nonneg_right (by exact_mod_cast hbad) (by positivity)


/-- A weaker compatibility form of Corollary 5.15: Gold families padded to rate
one half, including the additional `2 t ≤ d - 2` guard and the conservative
union-bound retained fraction `1 - ε`. The sharp endpoint below uses the exact
subspace-retention probability. -/
theorem gold_half_rate
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2) (hpad : 2 * t ≤ d - 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0))
    (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let δ : ℕ := N / 2 ^ (2 * t)
    let q : ℕ := Fintype.card F
    let Z := ⌈(L : ℚ) * (q - N) / (q - N + δ * (L - 1))⌉₊ - 1
    let ε : ℚ := 3 * (4 ^ t - 1) / (N - 1)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N / 2) f g (N / 2) ∧
      ⌈(1 - ε) * Z⌉₊ ≤
        (nonzeroBadChallenges E (N / 2) f g (5 * N / 8 - 3 * N / 2 ^ (t + 3))).card := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  dsimp only
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
  exact Gold.gold_half_rate_from_tensor_lower_bound φ D a d t hDN e ht hpad hq _ hL

/-- Half-rate Gold counterexamples with both simultaneous collision bounds, no challenge lost at
zero, and the exact subspace-retention probability. -/
theorem gold_half_rate_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2) (hpad : 2 * t ≤ d - 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0))
    (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let δ : ℕ := N / 2 ^ (2 * t)
    let q : ℕ := Fintype.card F
    let Z := max (L-(δ*L.choose 2)/(q-N)) ⌈(L : ℚ) * (q - N) / (q - N + δ * (L - 1))⌉₊
    let p := paddingRetentionProbability d (d-2) (2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N / 2) f g (N / 2) ∧
      ⌈p * Z⌉₊ ≤
        (nonzeroBadChallenges E (N / 2) f g (5 * N / 8 - 3 * N / 2 ^ (t + 3))).card := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  dsimp only
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
  exact Gold.gold_half_rate_from_tensor_lower_bound_sharp φ D a d t hDN e ht hpad hq _ hL

/-- The strengthened native example realizes the exact retained count, exceeds
`3.4248 × 10^29` challenges, and preserves the bounds on the inputs and probability claim.
The concrete `Gold.nativeGoldPaddedCountSharp` is `ceil(p * Z)`, where
`p = paddingRetentionProbability 27 19 12` and `Z` is the maximum of the two
collision bounds with no zero loss. Its separately proved exact value is
`342482627693920113354525730019`. -/
theorem native128Example_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hB : Fintype.card B = 2 ^ 32)
    (hF : Fintype.card F = 2 ^ 128)
    (D : AddSubgroup B) (a : B) (hD : (additiveDomain D).card = 2 ^ 27) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let N : ℕ := 2 ^ 27
    let K : ℕ := 2 ^ 25
    let q : ℕ := 2 ^ 128
    let Bcount := Gold.nativeGoldPaddedCountSharp
    ∃ f g : E → F,
      commonAgreementEQ E K f g K ∧ agreementEQ E K g K ∧
      agreementLE E K f (193 * N / 512 - 1) ∧
      Bcount ≤ (nonzeroBadChallenges E K f g (16193 * N / 32768)).card ∧
      (34248 * 10 ^ 25 : ℕ) < Bcount ∧
      Real.rpow 2 (-(29889 / 1000 : ℝ)) <
        ((nonzeroBadChallenges E K f g (16193 * N / 32768)).card : ℝ) / q := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype D := Fintype.ofFinite D
  have hDN : Nat.card D=2^27 := by rwa [card_additiveDomain] at hD
  obtain ⟨e⟩ := Gold.exists_gold_basis D 27 hDN
  have hpopulation := Gold.card_momentTensors_lower_bound D 32 27 6 hB hDN e
    (by decide) (by decide) (by norm_num [show ¬Even 27 by decide])
  have hL : Gold.nativeGoldListSize≤(Gold.momentTensors D (Gold.basisParameter D e) 6).card*2^12 := by
    have hp : 3*gaussianBinomial 4 13 6≤(Gold.momentTensors D (Gold.basisParameter D e) 6).card := by
      simpa only [show ¬Even 27 by decide,ite_false,Nat.reduceSub,Nat.reduceAdd,Nat.reduceMul,
        Nat.reducePow,Nat.reduceDiv] using hpopulation
    dsimp only [Gold.nativeGoldListSize]
    calc
      _ = (3*gaussianBinomial 4 13 6)*2^12 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := Gold.native_pair_from_tensor_lower_bound_sharp φ D a hDN e hF hL
  dsimp only
  refine ⟨f,g,hcommon,hg,hf,hbad,Gold.nativeGoldPaddedCountSharp_certificate.1,?_⟩
  apply Gold.nativeGoldPaddedCountSharp_certificate.2.trans_le
  rw [Nat.cast_pow,Nat.cast_ofNat]
  apply div_le_div_of_nonneg_right (by exact_mod_cast hbad) (by positivity)



end BinaryFieldCounterexamples
