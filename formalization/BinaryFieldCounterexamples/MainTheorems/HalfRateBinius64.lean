/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.Native128Example
public import BinaryFieldCounterexamples.Constructions.Gold.HalfRateBiniusCertificate

/-!
# Main theorem: the half-rate Binius64 numerical example

The Binius64 paragraph in Section 7.1 specializes
[Corollary 5.15, p. 46](../../../binary-field-counterexamples.pdf#page=46)
with `m = 32`, `d = 27`, `t = 6`, padding dimension `25`, and challenge
field size `2^128`. `halfRateBinius64` proves every exact fraction and
conservative decimal bound in that paragraph.

For every binary additive 27-space in a field of size `2^32`, every affine
translate, and a specified embedding into a field of size `2^128`, one fixed
pair has common agreement `N/2` for strict degree `< N/2`. At threshold
`317 N/512`, its nonzero exceptional set has at least the exact retained bound
`345129489779595974011716533694`, hence more than `3.45123 × 10^29` challenges
and uniform probability greater than `2^(-29.877)`. The fractional
common-agreement gap is exactly `61/512`.

The proof specializes `gold_half_rate_sharp`, then applies the kernel-checked
integer and rational certificates in `Gold.HalfRateBiniusCertificate`. The
received words take values in the challenge field. This is a theorem about
words and polynomial agreement; implementation reachability is separate.
All declarations here are proved, with no admitted targets.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- One fixed pair realizes the paper's half-rate Binius64 numerical bounds.
The count is a lower bound on distinct nonzero challenges, and the probability
uses uniform sampling from the entire challenge field, including zero.
The two fraction equalities record the agreement and gap of this same pair. -/
theorem halfRateBinius64
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hB : Fintype.card B = 2^32)
    (hF : Fintype.card F = 2^128)
    (D : AddSubgroup B) (a : B) (hD : (additiveDomain D).card = 2^27) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let N : ℕ := 2^27
    let K : ℕ := N/2
    let T : ℕ := 317*N/512
    ∃ f g : E → F,
      commonAgreementEQ E K f g K ∧
      345129489779595974011716533694 ≤ (nonzeroBadChallenges E K f g T).card ∧
      345123*10^24 < (nonzeroBadChallenges E K f g T).card ∧
      Real.rpow 2 (-(29877/1000:ℝ)) <
        ((nonzeroBadChallenges E K f g T).card:ℝ)/(Fintype.card F:ℝ) ∧
      (T:ℚ)/N = 317/512 ∧ (K:ℚ)/N = 1/2 ∧
      (T:ℚ)/N - (K:ℚ)/N = 61/512 := by
  classical
  -- Specialize the general construction before evaluating its retained count.
  have hq : 2^27 < Fintype.card F := by rw [hF]; norm_num
  obtain ⟨f,g,hcommon,hbad⟩ := gold_half_rate_sharp φ D a 32 27 6 hB hD
    (by decide) (by decide) (by decide)
    (by norm_num [show ¬Even 27 by decide]) hq
  have hb : Gold.halfRateBiniusCount ≤
      (nonzeroBadChallenges
        (mappedDomain φ (affineDomain (additiveDomain D) a))
        (2^27/2) f g (317*2^27/512)).card := by
    norm_num only [hF, show ¬Even 27 by decide, ite_false,
      Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reducePow,
      Nat.cast_pow, Nat.cast_ofNat,
      Gold.halfRateBiniusCount, Gold.nativeGoldPoleCountSharp, Gold.nativeGoldListSize]
      at hbad ⊢
    exact hbad
  dsimp only
  refine ⟨f,g,hcommon,?_,Gold.halfRateBiniusCount_lower.trans_le hb,?_,?_,?_,?_⟩
  · simpa only [Gold.halfRateBiniusCount_value] using hb
  -- Transfer the certified probability to the exceptional set of that pair.
  · apply Gold.halfRateBiniusCount_certificate.2.trans_le
    rw [hF, Nat.cast_pow, Nat.cast_ofNat]
    apply div_le_div_of_nonneg_right (by exact_mod_cast hb) (by positivity)
  · norm_num
  · norm_num
  · norm_num

end BinaryFieldCounterexamples
