/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Repairs
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.Hyperplanes
/-!
# Complete polynomial clauses for Gold labels and quadratic functions

Theorems below assemble Lemma 5.5(3) and Lemma 5.6(1) for the actual
label and quadratic polynomials of the manuscript.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Lemma 5.5(3): a nonzero label has degree `N/2` and leading coefficient `ηω`. -/
theorem parameterPolynomial_degree_and_leadingCoeff
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1))
    (c : parameterDomain D) (hc : c ≠ 0) :
    (parameterPolynomial D c).natDegree = 2^k ∧
      (parameterPolynomial D c).leadingCoeff = normalizingRoot D * (c : B) := by
  have hl : (parameterEquiv D).symm c ≠ 0 := by
    intro h
    apply hc
    simpa using congrArg (parameterEquiv D) h
  have hd : (parameterPolynomial D c).natDegree = 2^k := by
    rw [parameterPolynomial, ExactHalf.natDegree_functionalPolynomial_of_ne D _ hl, hD,
      pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  refine ⟨hd, ?_⟩
  rw [← coeff_natDegree, hd]
  exact parameterPolynomial_top_coeff D k hD c
/-- Lemma 5.6(1): the full quadratic polynomial, including its linear label,
 has strict degree below the domain, vanishes at zero, and evaluates to `ψ`. -/
theorem quadraticPolynomial_properties (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) :
    (repairedPolynomial D v A l 0).degree < Nat.card D ∧
      (repairedPolynomial D v A l 0).eval 0 = 0 ∧
      ∀ x : D, (repairedPolynomial D v A l 0).eval (x : B) =
        algebraMap (ZMod 2) B (tensorQuadraticFunction D v A x + l x) := by
  have he : repairedPolynomial D v A l 0 = tensorPolynomial D v A + functionalPolynomial D l := by
    simp [repairedPolynomial]
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact (degree_add_le _ _).trans_lt (max_lt (tensorPolynomial_degree_lt D k hD v A) (functionalPolynomial_degree_lt D l))
  · rw [he, eval_add, ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero,
      tensorPolynomial_coeff_zero, functionalPolynomial_coeff_zero, add_zero]
  · intro x
    simpa using repairedPolynomial_eval D v A l 0 x
end BinaryFieldCounterexamples.Gold
