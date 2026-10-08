/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.DenseAllRates.FinitePadding
public import BinaryFieldCounterexamples.Agreement.AffineTransport

/-!
# Outside padding and affine transport of ordinary decoding lists

Any padding set outside a seed domain adds its full cardinality to the degree
budget and to every seed agreement count. Multiplication by its nonzero nodal
polynomial preserves every distinct explaining polynomial. This construction
does not require balanced padding inside the seed domain.

Literal polynomial translation transports a decoding list to the corresponding
affine domain, preserving its cardinality, strict degree bounds and agreements.
These are the finite transfers used by Corollary 5.17.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.GoldAllRates
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Multiplication by the nodal polynomial of any set outside the seed domain
preserves the exact family cardinality and adds all padding coordinates to every
seed agreement lower bound. The received word is extended to the larger domain. -/
theorem finite_family_outside_padding {B : Type*} [Field B]
    (D S P : Finset B) (hSD : S ⊆ D) (hP : P ⊆ D \ S)
    (word : S → B) (E : Finset B[X]) (K T : ℕ)
    (hE : ∀ p ∈ E, p.degree < K ∧ T ≤ agreementCount S word p) :
    ∃ (word' : D → B) (E' : Finset B[X]), E'.card = E.card ∧
      ∀ p ∈ E', p.degree < P.card + K ∧
        P.card + T ≤ agreementCount D word' p := by
  let f : B → B := fun x => if hx : x ∈ S then word ⟨x, hx⟩ else 0
  let A := Lagrange.nodal P id
  have hf : (fun x : S => f x) = word := by
    funext x
    simp [f, x.property]
  refine ⟨fun x => A.eval x.val * f x.val, E.image (fun q => A * q), ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (fun _ _ h =>
      mul_left_cancel₀ Lagrange.nodal_ne_zero h)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨degree_nodal_mul_lt P K q (hE q hq).1, ?_⟩
    rw [agreementCount_nodal_mul_eq_card_union D P
      (fun x hx => (Finset.mem_sdiff.mp (hP hx)).1) f q]
    have hdisj : Disjoint P (S.filter fun x => q.eval x = f x) := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxS
      exact (Finset.mem_sdiff.mp (hP hxP)).2 (Finset.mem_filter.mp hxS).1
    have hsub : P ∪ (S.filter fun x => q.eval x = f x) ⊆
        P ∪ (D.filter fun x => q.eval x = f x) := by
      apply Finset.union_subset_union_right
      intro x hx
      obtain ⟨hxS, he⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hSD hxS, he⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      ← agreementCount_eq_card_filter S f q, hf] at hcard
    exact (Nat.add_le_add_left (hE q hq).2 P.card).trans hcard

/-- Select an exact-size seed family and any prescribed number of coordinates
outside its domain. The resulting ordinary list has agreement threshold and
strict degree budget raised by precisely that padding size. -/
theorem finite_list_outside_padding {B : Type*} [Field B]
    (D S : Finset B) (hSD : S ⊆ D) (word : S → B) (E : Finset B[X])
    (K T w L : ℕ)
    (hE : ∀ p ∈ E, p.degree < K ∧ T ≤ agreementCount S word p)
    (hL : L ≤ E.card) (hw : w ≤ (D \ S).card) :
    ordinaryList D (w + K) (w + T) L := by
  obtain ⟨I, hIE, hI⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨P, hP, hPcard⟩ := Finset.exists_subset_card_eq hw
  obtain ⟨word', E', hcard, hprop⟩ := finite_family_outside_padding
    D S P hSD hP word I K T (fun p hp => hE p (hIE hp))
  refine ⟨word', E', ?_, ?_⟩
  · exact le_of_eq (hcard.trans hI).symm
  · simpa only [hPcard, Nat.cast_add] using hprop

end BinaryFieldCounterexamples.GoldAllRates

namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Translation by `a` transports each explaining polynomial by literal
composition with `X - C a`, preserving the exact family cardinality, every
strict degree bound, and every agreement lower bound on the shifted domain. -/
theorem ordinary_family_affineDomain {B : Type*} [Field B]
    (D : Finset B) (a : B) (word : D → B) (E : Finset B[X]) (K T : ℕ)
    (hE : ∀ p ∈ E, p.degree < K ∧ T ≤ agreementCount D word p) :
    ∃ (word' : affineDomain D a → B) (E' : Finset B[X]), E'.card = E.card ∧
      ∀ p ∈ E', p.degree < K ∧ T ≤ agreementCount (affineDomain D a) word' p := by
  let f : B → B := fun x => if hx : x ∈ D then word ⟨x, hx⟩ else 0
  have hf : (fun x : D => f x) = word := by
    funext x
    simp [f, x.property]
  have hcomp (p : B[X]) : (p.comp (X - C a)).comp (X + C a) = p := by
    rw [comp_assoc]
    simp
  refine ⟨fun x => f (x.val - a), E.image (fun p => p.comp (X - C a)), ?_, ?_⟩
  · apply Finset.card_image_of_injective
    intro p q h
    have he := congrArg (fun s : B[X] => s.comp (X + C a)) h
    simpa only [hcomp] using he
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨?_, ?_⟩
    · rw [degree_comp (by simp), degree_X_sub_C, mul_one]
      exact (hE q hq).1
    · rw [agreementCount_affineDomain, hcomp, hf]
      exact (hE q hq).2

/-- An ordinary decoding list on any finite evaluation domain transports to
every translate, retaining the same list-size lower bound and integer degree
and agreement parameters. -/
theorem ordinaryList_affineDomain {B : Type*} [Field B]
    (D : Finset B) (a : B) (K T L : ℕ) (h : ordinaryList D K T L) :
    ordinaryList (affineDomain D a) K T L := by
  obtain ⟨word, E, hL, hE⟩ := h
  obtain ⟨word', E', hcard, hprop⟩ := ordinary_family_affineDomain D a word E K T hE
  exact ⟨word', E', hcard ▸ hL, hprop⟩

end BinaryFieldCounterexamples
