/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.DenseAllRates.FinitePadding
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.OrdinaryPolePair

/-!
# Finite higher-rate lengthening

A decoding list on a subset is lengthened to a prescribed larger domain by
multiplication by the nodal polynomial of its complement. Every new coordinate
agrees, while the original agreement count and number of distinct explaining
polynomials are preserved. Balanced padding is performed inside the smaller domain first;
this is the finite mechanism of [Corollary 5.16, p. 47](../../../../binary-field-counterexamples.pdf#page=47),
“Higher rates on every dense binary domain”.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.HigherRateLengthening
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Complement lengthening adds precisely the number of new coordinates to
both the degree budget and each explaining polynomial's agreement count. -/
theorem finite_list_lengthening {B : Type*} [Field B]
    (D S : Finset B) (hSD : S ⊆ D) (w : S → B) (E : Finset B[X]) (K : ℕ)
    (hE : ∀ p ∈ E, p.degree < K) :
    ∃ (w' : D → B) (E' : Finset B[X]), E'.card = E.card ∧
      ∀ p ∈ E', p.degree < (D \ S).card + K ∧
        ∃ q ∈ E, agreementCount D w' p = (D \ S).card + agreementCount S w q := by
  let f : B → B := fun x => if hx : x ∈ S then w ⟨x, hx⟩ else 0
  let A := Lagrange.nodal (D \ S) id
  have hf : (fun x : S => f x) = w := by
    funext x
    simp [f, x.property]
  refine ⟨fun x => A.eval x.val * f x.val, E.image (fun q => A * q), ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (fun _ _ h =>
      mul_left_cancel₀ Lagrange.nodal_ne_zero h)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨degree_nodal_mul_lt (D \ S) K q (hE q hq), q, hq, ?_⟩
    rw [agreementCount_nodal_mul_eq_card_union D (D \ S) (Finset.sdiff_subset) f q]
    have hunion : (D \ S) ∪ (D.filter fun x => q.eval x = f x) =
        (D \ S) ∪ (S.filter fun x => q.eval x = f x) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro (h | ⟨hxD, he⟩)
        · exact Or.inl h
        · by_cases hxS : x ∈ S
          · exact Or.inr ⟨hxS, he⟩
          · exact Or.inl ⟨hxD, hxS⟩
      · rintro (h | ⟨hxS, he⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hSD hxS, he⟩
    rw [hunion, Finset.card_union_of_disjoint]
    · rw [← agreementCount_eq_card_filter S f q, hf]
    · exact Finset.disjoint_left.mpr (by
        intro x hx hy
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mp hy).1)

/-- Balance extra degree inside the seed domain, then add the complement.
The resulting list keeps its exact selected size and the complete finite
agreement formula, including the square-root deviation. -/
theorem finite_balanced_lengthening {B : Type*} [Field B]
    (D S : Finset B) (hSD : S ⊆ D) (w : S → B) (E : Finset B[X])
    (K a T L : ℕ) (hE : ∀ p ∈ E, p.degree < K ∧ T ≤ agreementCount S w p)
    (hL : L ≤ E.card) (ha : a ≤ S.card) :
    let U : ℝ := (D \ S).card + a + T -
      ((a : ℝ) * T / S.card + Real.sqrt (((a : ℝ) / 2) * Real.log (2 * L)))
    ordinaryList D ((D \ S).card + (K + a)) ⌊U⌋₊ L := by
  dsimp only
  obtain ⟨w0, E0, hcard, hprop⟩ := DenseConstruction.finite_list_balanced_padding
    S w E K (K + a) T L hE hL (by omega) (by simpa using ha)
  obtain ⟨w1, E1, hcard1, hprop1⟩ := finite_list_lengthening D S hSD w0 E0
    (K + a) (fun p hp => (hprop p hp).1)
  apply DenseConstruction.ordinaryList_of_real_bound D _ L _ w1 E1 (hcard1.trans hcard)
  intro p hp
  obtain ⟨hdegree, q, hq, hagree⟩ := hprop1 p hp
  refine ⟨hdegree, ?_⟩
  rw [hagree, Nat.cast_add]
  have hbound := (hprop q hq).2
  simp only [Nat.add_sub_cancel_left] at hbound
  linarith

end BinaryFieldCounterexamples.HigherRateLengthening
