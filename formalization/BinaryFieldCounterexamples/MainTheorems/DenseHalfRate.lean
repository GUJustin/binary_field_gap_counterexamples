/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.DenseHalfRate

/-!
# Main theorem: Dense Gold families at rate one half

## Manuscript correspondence and full quantitative contract

[Corollary 5.15, p. 46](../../../binary-field-counterexamples.pdf#page=46),
the consequently clause, is proved here. For fixed codimension `c`, every
sufficiently large binary `d`-space in a field of size `2^(d+c)` supports a
received pair in an actual finite extension, with message length `N/2` and
common agreement exactly `N/2`, where `N=2^d`.

Put `θ=min(1/4,1/(c+1))` and `E=θ(1-2θ)d²`. The threshold is
`T/N=5/8-Θ_c(N^(-θ))`; the gap above common agreement is
`1/8-Θ_c(N^(-θ))`. The distinct nonzero exceptional count is at least
`2^(E-Cd)`, its probability is at least `p N^(-1+2θ)`, and the challenge
field lies between `2^(E-Cd)` and `2^(E+Cd)`. Constants and dimension cutoff
are uniform over the prescribed field, domain, and every affine translate.

## Proof stages

The finite assembly uses the same rounded extension field as Corollary 5.2,
but applies the actual padded-pair theorem of Corollary 5.15. The exact
subspace retention exceeds one quarter. The collision-energy bound therefore
still supplies `q/(32δ)` exceptional challenges, with `δ=N/2^(2t)`.
The dense parameter bounds preserve the quadratic leading exponent. The
normalized half-rate deficit is three quarters of the quarter-rate deficit.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- The complete dense consequently clause of Corollary 5.15, with the
agreement deficit and common-agreement gap stated together. One received pair
is fixed before every counted challenge; all Reed–Solomon degree bounds are
strict, through the concrete semantics in `PaperSemantics`. -/
theorem gold_half_rate_dense_asymptotic (c : ℕ) :
    let θ : ℝ := min (1 / 4) (1 / (c + 1))
    ∃ A C p : ℝ, 0 < A ∧ 0 < C ∧ 0 < p ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2 ^ (d + c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2 ^ d →
    ∀ a : B,
    let N : ℕ := 2 ^ d
    let E : ℝ := θ * (1 - 2 * θ) * (d : ℝ) ^ 2
    ∃ T : ℕ,
      A * (N : ℝ) ^ (-θ) ≤ 5 / 8 - (T : ℝ) / N ∧
      5 / 8 - (T : ℝ) / N ≤ C * (N : ℝ) ^ (-θ) ∧
      A * (N : ℝ) ^ (-θ) ≤ 1 / 8 - ((T : ℝ) / N - 1 / 2) ∧
      1 / 8 - ((T : ℝ) / N - 1 / 2) ≤ C * (N : ℝ) ^ (-θ) ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (affineDomain (additiveDomain D) a)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N / 2) f g (N / 2) ∧
        (2 : ℝ) ^ (E - C * d) ≤
          (nonzeroBadChallenges D' (N / 2) f g T).card ∧
        p * (N : ℝ) ^ (-1 + 2 * θ) ≤
          ((nonzeroBadChallenges D' (N / 2) f g T).card : ℝ) / Fintype.card F ∧
        (2 : ℝ) ^ (E - C * d) ≤ Fintype.card F ∧
        (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (E + C * d) := by
  dsimp only
  obtain ⟨A,C,p,hA,hC,hp,d₀,h⟩ := Gold.denseGold_halfRate_asymptotic c
  refine ⟨A,C,p,hA,hC,hp,d₀,?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD a
  obtain ⟨T,hlo,hhi,F,fieldF,finiteF,hrest⟩ := h d hd B hB D hD a
  refine ⟨T,hlo,hhi,?_,?_,F,fieldF,finiteF,hrest⟩ <;> linarith

end BinaryFieldCounterexamples
