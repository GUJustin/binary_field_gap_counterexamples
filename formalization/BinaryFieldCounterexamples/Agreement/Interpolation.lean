/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Agreement attained by interpolation

Any word, or pair of words, can be interpolated simultaneously on an arbitrary
number of coordinates up to the domain size.  Combined with the reciprocal
root bound, this gives exact individual and common agreement at an exterior
pole.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Every word has a strict-degree interpolant on any prescribed number of
coordinates up to the domain size. -/
theorem agreementGE_of_le_card
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (w : D → F)
    (hK : K ≤ D.card) : agreementGE D K w K := by
  classical
  have hcard : K ≤ (Finset.univ : Finset D).card := by simpa using hK
  obtain ⟨S, _, hScard⟩ := Finset.exists_subset_card_eq hcard
  let p := Lagrange.interpolate S Subtype.val w
  have hp : p.degree < K := by
    simpa only [p, hScard] using
      Lagrange.degree_interpolate_lt (s := S) (v := Subtype.val) w
        Subtype.val_injective.injOn
  refine ⟨p, hp, ?_⟩
  unfold agreementCount Code.agree
  rw [← hScard]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Lagrange.eval_interpolate_at_node w Subtype.val_injective.injOn hx).symm

/-- Two arbitrary words have simultaneous strict-degree interpolants on the
same chosen coordinates. -/
theorem commonAgreementGE_of_le_card
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (f g : D → F)
    (hK : K ≤ D.card) : commonAgreementGE D K f g K := by
  classical
  have hcard : K ≤ (Finset.univ : Finset D).card := by simpa using hK
  obtain ⟨S, _, hScard⟩ := Finset.exists_subset_card_eq hcard
  let p := Lagrange.interpolate S Subtype.val f
  let r := Lagrange.interpolate S Subtype.val g
  have hp : p.degree < K := by
    simpa only [p, hScard] using
      Lagrange.degree_interpolate_lt (s := S) (v := Subtype.val) f
        Subtype.val_injective.injOn
  have hr : r.degree < K := by
    simpa only [r, hScard] using
      Lagrange.degree_interpolate_lt (s := S) (v := Subtype.val) g
        Subtype.val_injective.injOn
  refine ⟨p, r, hp, hr, ?_⟩
  unfold commonAgreementCount Code.agree
  rw [← hScard]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Prod.ext
  · exact (Lagrange.eval_interpolate_at_node f Subtype.val_injective.injOn hx).symm
  · exact (Lagrange.eval_interpolate_at_node g Subtype.val_injective.injOn hx).symm

/-- The reciprocal word at a pole outside the domain has agreement exactly
`K`, whenever the domain contains at least `K` coordinates. -/
theorem agreementEQ_reciprocal
    {F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : K ≤ D.card) :
    agreementEQ D K (fun x ↦ ((x : F) - β)⁻¹) K := by
  exact ⟨agreementGE_of_le_card D K _ hK, agreementLE_reciprocal D β hβ K⟩

/-- With an arbitrary first word and a reciprocal second word, exact common
agreement is `K`: interpolation attains `K`, and the reciprocal bound caps it. -/
theorem commonAgreementEQ_reciprocal_right
    {F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : K ≤ D.card) (f : D → F) :
    commonAgreementEQ D K f (fun x ↦ ((x : F) - β)⁻¹) K := by
  exact ⟨commonAgreementGE_of_le_card D K f _ hK,
    commonAgreementLE_of_right D K f _ K (agreementLE_reciprocal D β hβ K)⟩

end BinaryFieldCounterexamples
