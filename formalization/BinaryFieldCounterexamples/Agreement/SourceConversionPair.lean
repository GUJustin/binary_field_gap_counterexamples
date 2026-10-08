/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.SourceConversion
/-!
# The conversion of Lemma 3.12 for pairs on a finite domain

Every proper finite field extension supplies an exterior scalar. Extending the
words away from their domain allows the checked conversion of Lemma 3.12 to produce
one mapped-domain pair whose two individual agreements equal the old common
agreement. The injective nonzero challenge transformation keeps the entire
old exceptional set, including zero.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_converted_pair_of_common_agreement
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B →+* F) (hsize : Fintype.card B<Fintype.card F)
    (D : Finset B) (K C T : ℕ) (f g : D → B)
    (hcommon : commonAgreementEQ D K f g C) :
    ∃ u v : mappedDomain φ D → F,
      agreementEQ (mappedDomain φ D) K u C ∧
      agreementEQ (mappedDomain φ D) K v C ∧
      commonAgreementEQ (mappedDomain φ D) K u v C ∧
      (badChallenges D K f g T).card≤
        (nonzeroBadChallenges (mappedDomain φ D) K u v T).card := by
  let : Algebra B F := φ.toAlgebra
  have hn : ¬Function.Surjective φ := by
    intro h
    exact (not_le_of_gt hsize) (Fintype.card_le_of_surjective φ h)
  simp only [Function.Surjective,not_forall,not_exists] at hn
  obtain ⟨θ,hθ⟩ := hn
  have hθrange : θ∉Set.range φ := by
    rintro ⟨x,hx⟩
    exact hθ x hx
  let f' : B → B := fun x => if hx : x∈D then f ⟨x,hx⟩ else 0
  let g' : B → B := fun x => if hx : x∈D then g ⟨x,hx⟩ else 0
  have hf : (fun x : D => f' x)=f := by funext x; simp [f',x.property]
  have hg : (fun x : D => g' x)=g := by funext x; simp [g',x.property]
  have hc : commonAgreementEQ D K (fun x => f' x) (fun x => g' x) C := by
    simpa only [hf,hg] using hcommon
  have ha := source_conversion_agreements D K C f' g' hc θ hθrange
  have halg : algebraMap B F=φ := RingHom.algebraMap_toAlgebra φ
  dsimp only at ha
  rw [halg] at ha
  have hb := card_badChallenges_le_converted_nonzeroBadChallenges φ θ hθrange D K T f' g'
  refine ⟨_,_,ha.1,ha.2.1,ha.2.2,?_⟩
  simpa only [hf,hg] using hb
end BinaryFieldCounterexamples
