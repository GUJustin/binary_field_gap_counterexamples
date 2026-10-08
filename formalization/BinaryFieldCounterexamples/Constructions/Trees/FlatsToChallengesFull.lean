/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.FlatsToChallenges
public import BinaryFieldCounterexamples.Constructions.Trees.HalfAgreementAsymptotic
/-!
# Lemma 6.1 including its simplified count

The same pair satisfies the full floor/ceiling bound and the final sentence's
`min {M/2,q/N}` bound for an arbitrary real collision budget. The numerical
hypothesis `2N ≤ q` is automatic for the paper's binary power sizes with `q>N`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
/-- Lemma 6.1, including the final sentence: the constructed fixed pair has
both the exact collision bound and the simplified minimum when `F ≤ NM²/8`. -/
theorem flats_to_challenges_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (D W : Finset F) (family : Finset (Finset F)) (T₀ w : ℕ) (budget : ℝ)
    (hw : 1 ≤ w) (hfamily : family.Nonempty) (hWD : W ⊆ D)
    (hq : D.card < Fintype.card F)
    (hA : ∀ S ∈ family, S ⊆ D \ W) (hsize : ∀ S ∈ family, S.card = T₀)
    (hne : ∀ S ∈ family, S.Nonempty)
    (hflats : ∀ S ∈ family, ∃ n : ℕ, ∃ A : Fin n → AffineSubspace (ZMod 2) F,
      (S : Set F) = ⋃ i, (A i : Set F) ∧
      (∀ i, (A i : Set F).Nonempty) ∧
      Pairwise (fun i j => Disjoint (A i : Set F) (A j : Set F)) ∧
      (∀ i, 2*w ≤ Nat.card (A i)))
    (hN : 0 < D.card) (hlarge : 2 * D.card ≤ Fintype.card F)
    (hsmall : budget ≤ (D.card : ℝ) * family.card ^ 2 / 8)
    (hE : ((T₀-w : ℕ) : ℝ)*family.card.choose 2 -
      ∑ x ∈ D \ W, (((family.filter fun S => x ∈ S).card).choose 2 : ℝ) ≤ budget) :
    0 ≤ budget ∧
    let K : ℕ := T₀-w+W.card
    let T : ℕ := T₀+W.card
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (T-1) ∧
      max (family.card-⌊budget/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℝ)*family.card^2/
          ((Fintype.card F-D.card)*family.card+2*budget)⌉₊ ≤ (nonzeroBadChallenges D K f g T).card ∧
      min ((family.card : ℝ) / 2) ((Fintype.card F : ℝ) / D.card) ≤
        ((nonzeroBadChallenges D K f g T).card : ℝ) := by
  classical
  obtain ⟨hzero, f, g, hc, hg, hf, hz⟩ := flats_to_challenges D W family T₀ w
    budget hw hfamily hWD hq hA hsize hne hflats hE
  refine ⟨hzero, f, g, hc, hg, hf, hz, ?_⟩
  exact (half_or_field_min_le_collision_bound_real D.card family.card
    (Fintype.card F) budget hN (Finset.card_pos.mpr hfamily) hlarge hzero hsmall).trans
      (Nat.cast_le.mpr hz)
/-- Lemma 6.1, literal binary-domain regime: `q>N` alone suffices for the
same-pair sharp minimum. Powers-of-two domain size is enough; no additive
structure of the domain is needed for this strengthening. -/
theorem flats_to_challenges_binary_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (d : ℕ) (D W : Finset F) (family : Finset (Finset F)) (T₀ w : ℕ) (budget : ℝ)
    (hw : 1 ≤ w) (hfamily : family.Nonempty) (hWD : W ⊆ D)
    (hq : D.card < Fintype.card F)
    (hA : ∀ S ∈ family, S ⊆ D \ W) (hsize : ∀ S ∈ family, S.card = T₀)
    (hne : ∀ S ∈ family, S.Nonempty)
    (hflats : ∀ S ∈ family, ∃ n : ℕ, ∃ A : Fin n → AffineSubspace (ZMod 2) F,
      (S : Set F) = ⋃ i, (A i : Set F) ∧
      (∀ i, (A i : Set F).Nonempty) ∧
      Pairwise (fun i j => Disjoint (A i : Set F) (A j : Set F)) ∧
      (∀ i, 2*w ≤ Nat.card (A i)))
    (hD : D.card = 2^d)
    (hsmall : budget ≤ (D.card : ℝ) * family.card ^ 2 / 8)
    (hE : ((T₀-w : ℕ) : ℝ)*family.card.choose 2 -
      ∑ x ∈ D \ W, (((family.filter fun S => x ∈ S).card).choose 2 : ℝ) ≤ budget) :
    0 ≤ budget ∧
    let K : ℕ := T₀-w+W.card
    let T : ℕ := T₀+W.card
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (T-1) ∧
      max (family.card-⌊budget/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℝ)*family.card^2/
          ((Fintype.card F-D.card)*family.card+2*budget)⌉₊ ≤ (nonzeroBadChallenges D K f g T).card ∧
      min ((family.card : ℝ) / 2) ((Fintype.card F : ℝ) / D.card) ≤
        ((nonzeroBadChallenges D K f g T).card : ℝ) := by
  apply flats_to_challenges_full D W family T₀ w budget hw hfamily hWD hq
    hA hsize hne hflats
  · rw [hD]; positivity
  · rw [hD]
    exact two_mul_pow_le_card_of_charTwo d (by rwa [hD] at hq)
  · exact hsmall
  · exact hE

end BinaryFieldCounterexamples
