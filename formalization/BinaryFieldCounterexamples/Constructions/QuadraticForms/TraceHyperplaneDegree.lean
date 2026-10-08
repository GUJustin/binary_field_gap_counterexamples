/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneFactors
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceDegree
/-!
# Exact degrees after hyperplane descent

The ambient minimum-rank trace polynomial and its derivative have proved exact
degrees. Literal composition by the degree-q hyperplane map divides both degrees
by q, with all natural subtractions justified by `1 ≤ t < n`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Exact descended polynomial and derivative degrees for a minimum-rank translate. -/
theorem descendedTracePolynomial_degrees_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t < n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (hne : a ≠ 0 ∨ c ≠ 0)
    (hrank : Module.finrank k B - Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical = 2*t)
    (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z)
    (hd : H.derivative.comp (hyperplanePolynomial (k := k) v) =
      (translatedTracePolynomial (k := k) n t a c z).derivative) :
    H.natDegree = (Fintype.card k)^(2*n-2)+(Fintype.card k)^(2*n-t-2) ∧
      H.derivative.natDegree = (Fintype.card k)^(2*n-t-1) := by
  have he' := congrArg Polynomial.natDegree he
  have hd' := congrArg Polynomial.natDegree hd
  rw [natDegree_comp, hyperplanePolynomial_natDegree v hv,
    translatedTracePolynomial_natDegree_of_exact_rank p r hr hq n t ht (by omega) a c z hcard hc hne hrank] at he'
  rw [natDegree_comp, hyperplanePolynomial_natDegree v hv,
    translatedTracePolynomial_derivative_natDegree_of_exact_rank p r hq n t ht (by omega) a c z hcard hc hne hrank] at hd'
  constructor
  · apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos (α := k))
    rw [he', Nat.add_mul, ← pow_succ, ← pow_succ]
    congr 1 <;> congr 1 <;> omega
  · apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos (α := k))
    rw [hd', ← pow_succ]
    congr 1
    omega
end BinaryFieldCounterexamples.QuadraticFormTrace
