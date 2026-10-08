/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticConversionCount
/-!
# Keeping factor data while quotienting locator conversion

The q−1 conversion fiber bound constructs a family of distinct locators while
keeping any proved property of a chosen factor/locator pair. Unlike a
decoding-list existential, this interface keeps the sparse factors required
for sharp collision counting.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial

/-- Quotient conversion multiplicity while keeping actual factor properties for every resulting locator. -/
theorem exists_locator_family_with_properties {F I : Type*} [Field F] [Fintype I]
    (G : I → F[X]) (L : F[X]) (q : ℕ) (hq : 2≤q)
    (property : F[X] → F[X] → Prop) (hinj : Function.Injective G) (hne : ∀ i, G i≠0)
    (hrep : ∀ i, ∃ A P : F[X], G i=A*P ∧ A^(q-1)*(P^q-L)=P ∧ property A P) :
    ∃ E : Finset F[X], (Fintype.card I : ℚ)/(q-1)≤E.card ∧
      ∀ P∈E, ∃ A : F[X], A^(q-1)*(P^q-L)=P ∧ property A P := by
  classical
  choose A P hG hconv hprop using hrep
  refine ⟨Finset.univ.image P, ?_, ?_⟩
  · have hn := converted_family_card_le G A P L q hq hinj hne hG hconv
    have hqRat : (0 : ℚ)<(q : ℚ)-1 := by
      have hh : (2 : ℚ) ≤ q := by exact_mod_cast hq
      linarith
    apply (div_le_iff₀ hqRat).mpr
    have hr : (Fintype.card I : ℚ) ≤ ((q-1 : ℕ) : ℚ)*(Finset.univ.image P).card := by exact_mod_cast hn
    simpa [Nat.cast_sub (by omega : 1≤q), mul_comm] using hr
  · intro Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨A i, hconv i, hprop i⟩
end BinaryFieldCounterexamples.QuadraticLocatorConversion
