/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticLocatorConversion
public import Mathlib.Data.Fintype.Card
public import BinaryFieldCounterexamples.Agreement.Basic
/-!
# Distinct quadratic explaining polynomials after locator conversion

Each converted locator has at most q−1 original polynomial representatives.
The actual finite fibers give a lower bound on distinct locators, which is
preserved when passing to strict-degree explaining polynomials of one common word.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Actual conversion fibers have at most q−1 distinct original polynomial representatives. -/
theorem converted_family_card_le {F I : Type*} [Field F] [Fintype I]
    (G A P : I → F[X]) (L : F[X]) (q : ℕ) (hq : 2≤q)
    (hinj : Function.Injective G) (hne : ∀ i,G i≠0)
    (hG : ∀ i,G i=A i*P i)
    (hconv : ∀ i,A i^(q-1)*(P i^q-L)=P i) :
    Fintype.card I≤(q-1)*(Finset.univ.image P).card := by
  classical
  have hfiber (Q : F[X]) (hQ : Q∈Finset.univ.image P) :
      (Finset.univ.filter (fun i => P i=Q)).card≤q-1 := by
    let E := Finset.univ.filter (fun i => P i=Q)
    obtain ⟨i,hi,hiQ⟩ := Finset.mem_image.mp hQ
    have hQ0 : Q≠0 := by
      intro hz
      have he := hG i
      rw [hiQ,hz,mul_zero] at he
      exact hne i he
    have hAinj : Set.InjOn A E := by
      intro i hi j hj hij
      apply hinj
      have hPi := (Finset.mem_filter.mp hi).2
      have hPj := (Finset.mem_filter.mp hj).2
      rw [hG i,hG j,hPi,hPj,hij]
    have hcard : (E.image A).card=E.card := Finset.card_image_iff.mpr hAinj
    rw [show (Finset.univ.filter (fun i => P i=Q)).card=E.card from rfl,←hcard]
    apply factor_fiber_card_le Q L q hq hQ0
    intro B hB
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hB
    have hjQ := (Finset.mem_filter.mp hj).2
    simpa only [hjQ] using hconv j
  calc
    Fintype.card I=∑ Q∈Finset.univ.image P,(Finset.univ.filter (fun i => P i=Q)).card := by
      simpa using Finset.card_eq_sum_card_image P (Finset.univ : Finset I)
    _≤∑ _Q∈Finset.univ.image P,(q-1) := Finset.sum_le_sum hfiber
    _=(q-1)*(Finset.univ.image P).card := by simp [Nat.mul_comm]

/-- Quotient conversion multiplicity and build a finite family of distinct strict-degree
explaining polynomials. -/
theorem exists_explanation_family_of_conversion {F I : Type*} [Field F] [Fintype I]
    (G : I → F[X]) (L R : F[X]) (D : Finset F) (q K T : ℕ) (hq : 2≤q)
    (hinj : Function.Injective G) (hne : ∀ i,G i≠0)
    (hfactor : ∀ i,∃ A P U : F[X], G i=A*P ∧ A^(q-1)*(P^q-L)=P ∧
      P=R+U ∧ U.degree<K ∧ agreementCount D (fun x => R.eval x.val) (-U)=T) :
    ∃ E : Finset F[X], (Fintype.card I : ℚ)/(q-1)≤E.card ∧
      ∀ f∈E,f.degree<K ∧ agreementCount D (fun x => R.eval x.val) f=T := by
  classical
  choose A P U hG hconv hPU hdU hagr using hfactor
  let E := Finset.univ.image (fun i => -U i)
  have hE : E=(Finset.univ.image P).image (fun Q => R-Q) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i hi
    dsimp
    rw [hPU]
    ring
  have hcard : E.card=(Finset.univ.image P).card := by
    rw [hE]
    exact Finset.card_image_iff.mpr (fun Q hQ S hS he => sub_right_injective he)
  have hcNat := converted_family_card_le G A P L q hq hinj hne hG hconv
  rw [←hcard] at hcNat
  refine ⟨E,?_,?_⟩
  · have hcRat : (Fintype.card I : ℚ)≤((q-1 : ℕ) : ℚ)*E.card := by exact_mod_cast hcNat
    have hqRat : (0 : ℚ)<(q : ℚ)-1 := by
      have hq2 : (2 : ℚ)≤q := by exact_mod_cast hq
      linarith
    apply (div_le_iff₀ hqRat).mpr
    simpa [Nat.cast_sub (by omega : 1≤q),mul_comm] using hcRat
  · intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨by simpa using hdU i,hagr i⟩
end BinaryFieldCounterexamples.QuadraticLocatorConversion
