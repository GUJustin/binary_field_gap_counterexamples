/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.HalfRateDecisionTrees
public import BinaryFieldCounterexamples.Agreement.SourceConversionPair

/-!
# Main theorem companion: the subfield paragraph after Theorem 6.10

Apply the tree construction in a proper subfield, then Lemma 3.12. The mapped
pair has both individual agreements equal to its common agreement. The
exceptional count keeps the original collision bound, using the subfield's
size rather than the challenge field's size.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- The paragraph following Theorem 6.10: tree counterexamples from a proper
subfield retain the finite count and give equal individual/common agreements
after conversion to the challenge field. -/
theorem half_rate_decision_trees_subfield
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hBF : Fintype.card B < Fintype.card F)
    (D : AddSubgroup B) (d h : ℕ) (hh : 2 ≤ h) (hd : 2 ^ h - 1 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hq : 2 ^ d < Fintype.card B) :
    let N : ℕ := 2 ^ d
    let K : ℕ := N / 2
    let w : ℕ := N / 2 ^ (h + 1)
    let M : ℕ := avoidingTreeSupportCount h d
    let q : ℕ := Fintype.card B
    let E : ℚ := (((K : ℚ) - w - (K : ℚ) ^ 2 / (N - w)) * M ^ 2 + w * M) / 2
    let A := mappedDomain φ (additiveDomain D)
    ∃ u v : A → F,
      agreementEQ A K u K ∧ agreementEQ A K v K ∧
      commonAgreementEQ A K u v K ∧
      max (M - ⌊E / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤
        (nonzeroBadChallenges A K u v (K + w)).card := by
  classical
  obtain ⟨f, g, hc, _, _, hb⟩ := half_rate_decision_trees D d h hh hd hD hq
  obtain ⟨u, v, hu, hv, huv, hbad⟩ := exists_converted_pair_of_common_agreement
    φ hBF (additiveDomain D) (2 ^ d / 2) (2 ^ d / 2)
      (2 ^ d / 2 + 2 ^ d / 2 ^ (h + 1)) f g hc
  refine ⟨u, v, hu, hv, huv, hb.trans ?_⟩
  exact (Finset.card_le_card (Finset.erase_subset 0 _)).trans hbad

end BinaryFieldCounterexamples
