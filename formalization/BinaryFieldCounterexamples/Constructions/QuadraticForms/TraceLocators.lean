/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceDegree
public import BinaryFieldCounterexamples.Polynomial.QuadraticFactorDegrees
public import BinaryFieldCounterexamples.Agreement.Basic
/-!
# Actual full-field locators from minimum-rank trace forms

Each literal minimum-rank translate supplies a locator with the exact elliptic
zero count and a strict-degree correction to one canonical numerator. The
negative correction is an actual explaining polynomial with exactly that many agreements.
The factor and conversion identity are kept for later multiplicity and
collision counting; this module does not assume the minimum-rank population.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- Construct the actual full-field locator and strict-degree explaining polynomial from a minimum-rank translate, at any numerator parameter. -/
theorem translatedTracePolynomial_exists_locator_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v β : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    let G := translatedTracePolynomial (k:=k) n t a c v
    let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
    ∃ A P U : B[X], A≠0 ∧ G=A*P ∧
      A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
      P=primePowerQuarterNumerator p r L β+U ∧ U.degree<(Fintype.card k)^(2*n-2) ∧
      A.natDegree=(Fintype.card k)^(2*n-t-1) ∧
      (Finset.univ.filter (fun x : B => P.eval x=0)).card=
        (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) ∧
      agreementCount Finset.univ (fun x => (primePowerQuarterNumerator p r L β).eval x.val) (-U)=
        (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  dsimp only
  let G := translatedTracePolynomial (k:=k) n t a c v
  let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
  obtain ⟨A,P,S,hA,hG,hJ,hS,hP⟩ := translatedTracePolynomial_exists_factors_of_exact_rank
    p r hr hq n t ht htn a c v hcard hc hne hrank
  have hlam : L.coeff 1≠0 := subspacePolynomial_coeff_one_ne_zero _
  obtain ⟨hdA,hdP,hdS⟩ := quadratic_factor_degrees (Fintype.card k) (2*n) t Fintype.one_lt_card
    ht (by omega) G G.derivative A P S (L.coeff 1) hlam hA hG hJ hS
    (translatedTracePolynomial_natDegree_of_exact_rank p r hr hq n t ht htn a c v hcard hc hne hrank)
    (translatedTracePolynomial_derivative_natDegree_of_exact_rank p r hq n t ht htn a c v hcard hc hne hrank)
  have hconv : A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P :=
    QuadraticLocatorConversion.conversion_identity G A P L (L.coeff 1) (Fintype.card k)
      Fintype.one_lt_card hlam hA hG hJ
      (translatedTracePolynomial_differential p r hr hq n t ht htn a c v hcard hc)
  have hsupp : ∀ e∈L.support,∃ i : ℕ,e=(p^r)^i := by
    intro e he
    obtain ⟨i,hi⟩ := FiniteFieldLocator.subspacePolynomial_q_support (⊤ : Submodule k B) e he
    exact ⟨i,by simpa only [hq] using hi⟩
  have hSlt : S.natDegree<p^r*(Fintype.card k)^(2*n-2) := by
    rw [hdS,←hq]
    have he : (Fintype.card k)*(Fintype.card k)^(2*n-2)=(Fintype.card k)^(2*n-1) := by
      rw [←pow_succ']; congr 1; omega
    rw [he]
    apply Nat.sub_lt (pow_pos Fintype.card_pos _)
    exact Nat.mul_pos (by have := Fintype.one_lt_card (α:=k); omega) (pow_pos Fintype.card_pos _)
  obtain ⟨U,hU,hdU⟩ := converted_quadratic_strict_correction p r hr P S L β
    ((Fintype.card k)^(2*n-2)) (pow_pos Fintype.card_pos _) hsupp (by simpa only [hq] using hP) hSlt
  refine ⟨A,P,U,hA,hG,hconv,hU,hdU,hdA,?_⟩
  have hsets : Finset.univ.filter (fun x : B => P.eval x=0)=
      Finset.univ.filter (fun x : B => G.eval x=0) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact QuadraticLocatorConversion.converted_isRoot_iff G A P L (Fintype.card k)
      Fintype.one_lt_card hG hconv x
  have hzero : (Finset.univ.filter (fun x : B => P.eval x=0)).card=
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
    rw [hsets]
    exact translatedTracePolynomial_zero_card_of_exact_rank p r hr hq n t ht htn a c v hcard hc hne hrank
  refine ⟨hzero,?_⟩
  rw [agreementCount_eq_card_filter Finset.univ
    (fun x : B => (primePowerQuarterNumerator p r L β).eval x) (-U)]
  convert hzero using 1
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,eval_neg,hU,eval_add]
  constructor <;> intro h <;> linear_combination -h
end BinaryFieldCounterexamples.QuadraticFormTrace
