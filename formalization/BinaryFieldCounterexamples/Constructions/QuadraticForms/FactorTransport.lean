/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FactorCollisions
public import BinaryFieldCounterexamples.Agreement.Domains

/-!
# Transport of quadratic conversion factors

Field embeddings preserve factor support divisibility, exact zero counts on a
prescribed finite domain, degrees, and the conversion identity.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Mapping a polynomial through a field embedding preserves support divisibility. -/
theorem map_factor_support_dvd
    {B F : Type*} [Field B] [Field F] (φ : B→+*F)
    (A : B[X]) (c : ℕ) (hA : ∀ e∈A.support,c∣e) :
    ∀ e∈(A.map φ).support,c∣e := by
  intro e he
  apply hA e
  rw [mem_support_iff] at he ⊢
  exact fun hz => he (by simp only [coeff_map,hz,map_zero])

/-- Mapping a polynomial and its finite evaluation domain preserves its exact
number of zeros. -/
theorem card_mapped_factor_zeros
    {B F : Type*} [Field B] [Field F]
    (φ : B→+*F) (D : Finset B) (A : B[X]) :
    ((mappedDomain φ D).filter fun x => (A.map φ).eval x=0).card=
      (D.filter fun x => A.eval x=0).card := by
  rw [mappedDomain]
  simp only [Finset.filter_image]
  have heq : (D.filter fun x => (A.map φ).eval (φ x)=0)=
      (D.filter fun x => A.eval x=0) := by
    ext x
    simp only [Finset.mem_filter]
    rw [eval_map,eval₂_at_apply,map_eq_zero]
  rw [heq]
  exact Finset.card_image_of_injective _ φ.injective

/-- Mapping all polynomials in a conversion identity preserves that identity. -/
theorem map_factor_conversion
    {B F : Type*} [Field B] [Field F] (φ : B→+*F)
    (A P L : B[X]) (b : ℕ) (h : A^(b-1)*(P^b-L)=P) :
    (A.map φ)^(b-1)*((P.map φ)^b-L.map φ)=P.map φ := by
  rw [←Polynomial.map_pow φ,←Polynomial.map_pow φ,←Polynomial.map_sub φ,
    ←Polynomial.map_mul φ]
  exact congrArg (Polynomial.map φ) h

end BinaryFieldCounterexamples.QuadraticLocatorConversion
