/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.DomainTranslation
public import BinaryFieldCounterexamples.MainTheorems.HalfRateBinius64
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting

/-!
# Main theorem companions: arbitrary affine translates

Theorem 5.1, Corollary 5.18, and the rate-one-half Binius64 example retain
all their quantitative conclusions after an arbitrary shift in the challenge
field. These companions preserve the existing statements and remove their
restriction to shifts in the embedded base field.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- Corollary 5.18 on every translate by an arbitrary challenge-field element: the exact individual/common agreements, exceptional count and certified probability all hold for one translated pair. -/
theorem native128Example_sharp_affine_translate
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hB : Fintype.card B = 2 ^ 32)
    (hF : Fintype.card F = 2 ^ 128)
    (D : AddSubgroup B) (a : B) (c : F) (hD : (additiveDomain D).card = 2 ^ 27) :
    let E := affineDomain (mappedDomain φ (affineDomain (additiveDomain D) a)) c
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
  obtain ⟨f, g, h⟩ := native128Example_sharp φ hB hF D a hD
  refine ⟨translatedWord _ c f, translatedWord _ c g, ?_⟩
  simpa only [commonAgreementEQ_translatedWord_iff, agreementEQ_translatedWord_iff,
    agreementLE_translatedWord_iff, nonzeroBadChallenges_translatedWord] using h

/-- Theorem 5.1 on every translate by an arbitrary challenge-field element, including both simultaneous collision bounds and both strict witness dimensions. -/
theorem gold_counting_sharp_affine_translate
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) (a : B) (c : F) (m d t : ℕ)
    (hB : Fintype.card B = 2 ^ m) (hD : (additiveDomain D).card = 2 ^ d)
    (ht : 2 ≤ t) (htd : t ≤ d / 2)
    (hΔ : 1 ≤ m - t * (m - d + if Even d then 1 else 0))
    (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let Δ : ℕ := m - t * (m - d + if Even d then 1 else 0)
    let L : ℕ := 2 ^ (2 * t) * (2 ^ Δ - 1) * gaussianBinomial 4 (d / 2) t
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let δ : ℕ := N / 2 ^ (2 * t)
    let E := affineDomain (mappedDomain φ (affineDomain (additiveDomain D) a)) c
    let q : ℕ := Fintype.card F
    let Z : ℕ := max (L-(δ*L.choose 2)/(q-N)) ⌈(L : ℚ) * ((q : ℚ) - (N : ℚ)) /
      ((q : ℚ) - (N : ℚ) + (δ : ℚ) * ((L : ℚ) - 1))⌉₊
    ∃ f g : E → F,
      commonAgreementEQ E (N / 4) f g (N / 4) ∧
      agreementEQ E (N / 4) g (N / 4) ∧
      agreementLE E (N / 4) f (3 * N / 8 - 1) ∧
      Z ≤ (nonzeroBadChallenges E (N / 4) f g T).card ∧
      Z ≤ (nonzeroBadChallenges E (T / 2) f g T).card := by
  obtain ⟨f, g, h⟩ := gold_counting_sharp φ D a m d t hB hD ht htd hΔ hq
  refine ⟨translatedWord _ c f, translatedWord _ c g, ?_⟩
  simpa only [commonAgreementEQ_translatedWord_iff, agreementEQ_translatedWord_iff,
    agreementLE_translatedWord_iff, nonzeroBadChallenges_translatedWord] using h

/-- The rate-one-half Binius64 example in Section 5.7 on every translate by an arbitrary challenge-field element, retaining the count, probability, and all fractions. -/
theorem halfRateBinius64_affine_translate
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hB : Fintype.card B = 2^32)
    (hF : Fintype.card F = 2^128)
    (D : AddSubgroup B) (a : B) (c : F) (hD : (additiveDomain D).card = 2^27) :
    let E := affineDomain (mappedDomain φ (affineDomain (additiveDomain D) a)) c
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
  obtain ⟨f, g, h⟩ := halfRateBinius64 φ hB hF D a hD
  refine ⟨translatedWord _ c f, translatedWord _ c g, ?_⟩
  simpa only [commonAgreementEQ_translatedWord_iff, agreementEQ_translatedWord_iff,
    agreementLE_translatedWord_iff, nonzeroBadChallenges_translatedWord] using h

end BinaryFieldCounterexamples
