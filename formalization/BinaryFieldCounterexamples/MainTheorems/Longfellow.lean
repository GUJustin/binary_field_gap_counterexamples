/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Longfellow.Seed
public import BinaryFieldCounterexamples.Constructions.Longfellow.Transfer
public import BinaryFieldCounterexamples.Constructions.Longfellow.Arithmetic
public import BinaryFieldCounterexamples.Constructions.Longfellow.Probability
/-!
# Main theorem: Longfellow's four binary extension domains

This proves the specialization in
[Corollary 5.19, p. 50](../../../binary-field-counterexamples.pdf#page=50) of the paper. Let `B` have
`2^16` elements and let the challenge field `F` have `2^128` elements. On every
prescribed domain `S` containing an embedded affine binary 11-space, for

* `(N,K) = (3230,461), (3318,474), (3352,478), (3436,490)`,

there is a fixed pair with common agreement exactly `K` and at least
5,843,376 distinct nonzero challenges giving agreement at least `K+384`
with a polynomial of degree strictly below `K`. The second input has agreement
exactly `K`. Thus the four thresholds are 845, 858, 862, and 874.
The probability corollary proves that the exceptional probability is strictly
greater than `2^(-105.522)` for a uniform challenge in `F`.

The endpoint quantifies over the actual domain; it does not replace it by an
additive domain. The affine-space inclusion is the mathematical condition
verified for Longfellow's binary-linear injection on indices `[2048,4096)`.
The configuration arithmetic is proved in `Longfellow.Arithmetic`. The pinned
implementation correspondence is documented in `docs/longfellow-parameters.md`.
This is a proximity-gap counterexample, not a complete-protocol attack.

The proof constructs the Gold family, pads its root sets with disjoint domain
points, and excludes every pole causing a zero challenge or a collision.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Longfellow
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The Longfellow specialization on each prescribed domain containing the
specified affine space. Field sizes, domain inclusion, and one of the four
actual `(length, dimension)` pairs are the only application hypotheses. -/
theorem longfellow_counterexample
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (S : Finset F) (K : ℕ)
    (hB : Fintype.card B=2^16) (hF : Fintype.card F=2^128)
    (hD : Nat.card D=2^11)
    (hUS : affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a) ⊆ S)
    (hconfig : (S.card,K) ∈ parameterPairs) :
    ∃ f g : S → F, commonAgreementEQ S K f g K ∧
      agreementEQ S K g K ∧
      5843376 ≤ (nonzeroBadChallenges S K f g (K+384)).card := by
  classical

  -- Construct the actual shared-coefficient family on the embedded affine space.
  let U := affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a)
  obtain ⟨R,ps,hcard,hps⟩ := exists_seed_family φ D a hB hD
  have hU : U.card=2048 := by
    rw [card_affineDomain,card_additiveDomain,natCard_map_addSubgroup,hD]
    norm_num
  obtain ⟨hk,hK,hpad,hbudget⟩ := configured_parameter_bounds hconfig
  rw [listSize_value] at hbudget
  have hpad' : K-384≤(S\U).card := by
    rw [Finset.card_sdiff_of_subset hUS,hU]
    exact hpad

  -- Disjoint padding raises agreement and degree together; the field is large
  -- enough to retain every one of the distinct nonzero challenges.
  have hp := exists_padded_pole_pair_of_polynomial_family S U ps R 384 K 768 5843376
    hUS (by decide) hk hK hpad' hcard.ge
    (fun p hp => (hps p hp).1) (fun p hp => (hps p hp).2)
    (by rw [hF]; exact hbudget)
  have hthreshold : K-384+768=K+384 := by omega
  simpa only [hthreshold] using hp

/-- The same fixed pair also has exceptional probability strictly greater than
`2^(-105.522)` for a uniform challenge from the entire 128-bit field. -/
theorem longfellow_counterexample_probability
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (S : Finset F) (K : ℕ)
    (hB : Fintype.card B=2^16) (hF : Fintype.card F=2^128)
    (hD : Nat.card D=2^11)
    (hUS : affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a) ⊆ S)
    (hconfig : (S.card,K) ∈ parameterPairs) :
    ∃ f g : S → F, commonAgreementEQ S K f g K ∧
      agreementEQ S K g K ∧
      5843376 ≤ (nonzeroBadChallenges S K f g (K+384)).card ∧
      (2 : ℝ)^(-105.522 : ℝ) <
        ((nonzeroBadChallenges S K f g (K+384)).card : ℝ)/(Fintype.card F : ℝ) := by
  obtain ⟨f,g,hcommon,hg,hcount⟩ := longfellow_counterexample φ D a S K hB hF hD hUS hconfig
  refine ⟨f,g,hcommon,hg,hcount,?_⟩
  apply probability_lower.trans_le
  rw [hF]
  push_cast
  have hcast : (5843376 : ℝ) ≤ ((nonzeroBadChallenges S K f g (K+384)).card : ℝ) := by
    exact_mod_cast hcount
  convert div_le_div_of_nonneg_right hcast
    (show (0 : ℝ) ≤ (2 : ℝ)^128 by positivity) using 1
  norm_num
end BinaryFieldCounterexamples
