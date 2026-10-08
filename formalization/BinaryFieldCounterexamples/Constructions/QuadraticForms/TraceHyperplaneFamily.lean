/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceDescent
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceTranslation
public import BinaryFieldCounterexamples.Polynomial.SparseCompositionDescent
/-!
# Actual trace-family descent through a prescribed radical line

A translated trace quadratic is constant on every coset of a scalar line
contained in its quadratic radical. It therefore descends literally through
the map onto the prescribed hyperplane. Its descended derivative has exactly
the allowed sparse support interval: nonconstant exponents q^i with
`t ≤ i ≤ 2n-t-1`. These are concrete polynomial statements, not extra
hypotheses about an unspecified family.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- A prescribed quadratic-radical line makes every actual translated trace polynomial constant on its fibers. -/
theorem translatedTracePolynomial_radical_fiber (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c z v x y : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n) = c)
    (hv : v ∈ (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical)
    (hxy : x-y ∈ Submodule.span k {v}) :
    (translatedTracePolynomial (k := k) n t a c z).eval x =
      (translatedTracePolynomial (k := k) n t a c z).eval y := by
  let Q := traceFamilyQuadraticForm n t ht htn a c hcard hc
  have hmem : x-y ∈ Q.radical := (Submodule.span_le.mpr (by intro w hw; rcases Set.mem_singleton_iff.mp hw with rfl; exact hv)) hxy
  have he := (QuadraticMap.mem_radical_iff'.mp hmem).2 (y-z)
  have heq : x-y+(y-z)=x-z := by ring
  rw [heq] at he
  rw [translatedTracePolynomial_eval, translatedTracePolynomial_eval,
    ← algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc,
    ← algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc]
  exact congrArg (algebraMap k B) he

/-- Every actual translate with the prescribed radical vector descends to the literal hyperplane, together with its derivative. -/
theorem translatedTracePolynomial_hyperplane_descent (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c z v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n) = c) (hv : v ≠ 0)
    (hvrad : v ∈ (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical)
    (D : Submodule k B) (hD : Module.finrank k D + 1 = Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) :
    ∃ H : B[X], H.natDegree < Nat.card D ∧
      H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z ∧
      H.derivative.comp (hyperplanePolynomial (k := k) v) =
        (translatedTracePolynomial (k := k) n t a c z).derivative := by
  apply hyperplane_polynomial_descent D hD v hv hrange
  · have hb := translatedTracePolynomial_degree_comparison n t ht htn a c z hcard
    have hq : 2 ≤ Fintype.card k := Fintype.one_lt_card
    nlinarith
  · intro x y hxy
    exact translatedTracePolynomial_radical_fiber n t ht htn a c z v x y hcard hc hvrad hxy
/-- The prescribed hyperplane map has literal q-power support. -/
theorem hyperplanePolynomial_q_support (v : B) :
    FiniteFieldLocator.IsQLinearized (k := k) (hyperplanePolynomial (k := k) v) := by
  unfold hyperplanePolynomial
  exact FiniteFieldLocator.isQLinearized_X.sub _ _
    ((FiniteFieldLocator.isQLinearized_X.pow_card _).c_mul _ _)

/-- The descended derivative has the required lower and upper Frobenius support indices. -/
theorem descendedTracePolynomial_derivative_support (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (H : B[X])
    (he : H.derivative.comp (hyperplanePolynomial (k := k) v) =
      (translatedTracePolynomial (k := k) n t a c z).derivative) :
    ∀ e ∈ H.derivative.support, e = 0 ∨ ∃ i : ℕ,
      t ≤ i ∧ i ≤ 2*n-t-1 ∧ e = (Fintype.card k)^i := by
  have hlin := traceFamily_derivative_q_support (k := k) n t ht htn a c
  have hconst : (translatedTracePolynomial (k := k) n t a c z).derivative -
      C ((translatedTracePolynomial (k := k) n t a c z).derivative.coeff 0) =
      (traceFamilyPolynomial (k := k) n t a c).derivative := by
    rw [translatedTracePolynomial_derivative n t ht htn a c z hcard]
    simp only [coeff_sub, coeff_C, ite_true, hlin.coeff_zero _, zero_sub, map_neg]
    ring
  apply FiniteFieldLocator.support_interval_of_comp (hyperplanePolynomial (k := k) v)
    H.derivative t (2*n-t-1) (hyperplanePolynomial_q_support v)
    (hyperplanePolynomial_natDegree v hv)
    (by rw [hyperplanePolynomial_derivative, eval_one]; exact one_ne_zero)
  · rwa [he, hconst]
  · rw [he, hconst, X_pow_dvd_iff]
    intro e hel
    by_contra hn
    have hes := mem_support_iff.mpr hn
    have he0 : e ≠ 0 := by intro h; subst e; exact hn (hlin.coeff_zero _)
    have hd := traceFamily_derivative_support_dvd n t ht htn a c e hes
    exact (not_le_of_gt hel) (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hd)
  · rw [he, translatedTracePolynomial_derivative n t ht htn a c z hcard, natDegree_sub_C]
    have hb := traceFamily_derivative_natDegree_le (k := k) n t ht htn a c
    convert hb using 1
    congr 1
    omega
end BinaryFieldCounterexamples.QuadraticFormTrace
