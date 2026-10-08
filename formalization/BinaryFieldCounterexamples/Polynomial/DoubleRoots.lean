/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Degree bounds from double roots

A polynomial and its derivative vanish together with multiplicity at least two,
even in positive characteristic. The Wronskian consequence supplies the binary
quarter-rate first-input bound without a characteristic-zero assumption.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- Distinct simultaneous zeros of a polynomial and its derivative each consume
at least two degrees, in arbitrary characteristic. -/
theorem twice_card_le_natDegree_of_double_roots
    {F : Type*} [Field F] (S : Finset F) (P : F[X]) (hP : P ≠ 0)
    (hroot : ∀ x ∈ S, P.eval x = 0)
    (hderiv : ∀ x ∈ S, P.derivative.eval x = 0) :
    2 * S.card ≤ P.natDegree := by
  classical
  have hdvd : (∏ x ∈ S, (X - C x : F[X]) ^ 2) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro x hx y hy hxy
      exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow
    · intro x hx
      apply (le_rootMultiplicity_iff hP).mp
      exact (one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hroot x hx, hderiv x hx⟩
  have := natDegree_le_of_dvd hdvd hP
  have heq : (∏ x ∈ S, (X - C x : F[X]) ^ 2) = (∏ x ∈ S, (X - C x : F[X])) ^ 2 := by
    rw [Finset.prod_pow]
  rw [heq, natDegree_pow, natDegree_finsetProd_X_sub_C_eq_card] at this
  simpa only [Nat.mul_comm] using this
/-- A Wronskian cancellation makes common roots double, with a degree bound
that applies in every characteristic. -/
theorem twice_card_le_of_wronskian
    {F : Type*} [Field F] (S : Finset F) (P Q : F[X]) (c β : F)
    (hc : c ≠ 0) (hQ' : Q.derivative = -C c)
    (hQβ : Q.eval β = 0) (hPβ : P.eval β ≠ 0)
    (hroot : ∀ x ∈ S, P.eval x = 0 ∧ Q.eval x = 0)
    (M A B : ℕ) (hPdeg : P.natDegree ≤ M)
    (hP'deg : P.derivative.natDegree ≤ A) (hQdeg : Q.natDegree ≤ B) :
    2 * S.card ≤ max (A + B) M := by
  let Ω := P.derivative * Q + C c * P
  have hΩβ : Ω.eval β = c * P.eval β := by simp [Ω, hQβ]
  have hΩ : Ω ≠ 0 := by
    intro h
    have := hΩβ
    rw [h, eval_zero] at this
    exact mul_ne_zero hc hPβ this.symm
  have hdΩ : Ω.derivative = P.derivative.derivative * Q := by
    simp only [Ω, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, hQ']
    ring
  have hc := twice_card_le_natDegree_of_double_roots S Ω hΩ
    (fun x hx => by simp [Ω, (hroot x hx).1, (hroot x hx).2])
    (fun x hx => by simp [hdΩ, (hroot x hx).2])
  apply hc.trans
  apply (natDegree_add_le _ _).trans
  apply max_le_max
  · exact (natDegree_mul_le).trans (Nat.add_le_add hP'deg hQdeg)
  · exact (natDegree_mul_le).trans (by simpa using hPdeg)
end BinaryFieldCounterexamples
