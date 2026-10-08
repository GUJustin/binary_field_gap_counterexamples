/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ExactRank
public import BinaryFieldCounterexamples.Polynomial.QuadraticFactorExistence
/-!
# Actual factors of minimum-rank translated trace polynomials

The derivative has its full radical-sized root set. Its proved multiplicities
show that it splits and divides the translated function polynomial. These are
actual polynomial facts needed before locator conversion.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The derivative of each actual minimum-rank translate splits in the ambient field. -/
theorem translatedTracePolynomial_derivative_splits_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative.Splits := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  let S := Finset.univ.filter (fun x : B => G.derivative.eval x=0)
  have hS : S.card=(Fintype.card k)^(2*n-2*t) :=
    translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn a c v
      hcard hc hne hrank
  have hd : G.derivative.natDegree≤(Fintype.card k)^(2*n-t) := by
    dsimp [G,translatedTracePolynomial]
    simp only [derivative_comp,derivative_sub,derivative_X,derivative_C,sub_zero,
      one_mul,natDegree_comp,natDegree_X_sub_C,mul_one]
    exact traceFamily_derivative_natDegree_le n t ht htn a c
  apply splits_of_primePower_full_card p (r*t) G.derivative
    (translatedTracePolynomial_derivative_ne_zero n t ht htn a c v hne) S
  · intro e he
    simpa [pow_mul,←hq] using
      translatedTracePolynomial_derivative_support_dvd n t ht htn a c v hcard e he
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · rw [pow_mul,←hq,hS,←pow_add]
    convert hd using 1
    congr 1
    omega

/-- The derivative divides the actual minimum-rank translated trace polynomial. -/
theorem translatedTracePolynomial_derivative_dvd_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative ∣
      translatedTracePolynomial (k:=k) n t a c v := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  apply dvd_of_splits_multiplicity_le G.derivative G
    (translatedTracePolynomial_derivative_ne_zero n t ht htn a c v hne)
    (translatedTracePolynomial_derivative_splits_of_exact_rank p r hq n t ht htn a c v
      hcard hc hne hrank)
  intro x
  by_cases hx : G.derivative.eval x=0
  · rw [translatedTracePolynomial_derivative_multiplicity_of_exact_rank p r hq n t ht htn
      a c v hcard hc hne hrank x hx,
      translatedTracePolynomial_multiplicity_of_exact_rank p r hr hq n t ht htn
      a c v hcard hc hne hrank x hx]
    omega
  · rw [rootMultiplicity_eq_zero hx]
    omega

/-- The actual minimum-rank translate admits Frobenius and quotient factors with the exact locator identity. -/
theorem translatedTracePolynomial_exists_factors_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    let G := translatedTracePolynomial (k:=k) n t a c v
    let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
    ∃ A P S : B[X], A≠0 ∧ G=A*P ∧ G.derivative= -C (L.coeff 1)*A^(Fintype.card k) ∧
      G=G.derivative*S ∧ P^(Fintype.card k)=L-C (L.coeff 1)*S := by
  dsimp only
  rw [hq]
  apply exists_converted_quadratic_factors p r
  · exact subspacePolynomial_coeff_one_ne_zero _
  · exact translatedTracePolynomial_derivative_ne_zero n t ht htn a c v hne
  · exact translatedTracePolynomial_derivative_dvd_of_exact_rank p r hr hq n t ht htn
      a c v hcard hc hne hrank
  · intro e he
    have hdiv : p^r ∣ (Fintype.card k)^t := by
      rw [←hq]
      exact dvd_pow_self _ (by omega)
    exact hdiv.trans (translatedTracePolynomial_derivative_support_dvd n t ht htn a c v hcard e he)
  · simpa only [←hq] using translatedTracePolynomial_differential p r hr hq n t ht htn
      a c v hcard hc
end BinaryFieldCounterexamples.QuadraticFormTrace
