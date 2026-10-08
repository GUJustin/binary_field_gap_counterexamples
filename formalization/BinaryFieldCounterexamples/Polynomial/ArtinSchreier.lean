/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.BinarySupport

/-!
# Quadratic identities for binary locators

Polynomial Artin--Schreier identities distinguish exterior evaluations of affine
hyperplane locators and recover additivity from a polynomial equation. These are
polynomial identities, not merely identities of functions on the finite field.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- Solutions to one quadratic polynomial equation differ by a constant. -/
theorem artinSchreier_difference
    {F : Type*} [Field F] [CharP F 2] (A B L : F[X]) (c : F)
    (hA : A ^ 2 + C c * A = L) (hB : B ^ 2 + C c * B = L) :
    A + B = 0 ∨ A + B = C c := by
  have h : (A + B) * (A + B + C c) = 0 := by
    calc
      _ = (A ^ 2 + C c * A) + (B ^ 2 + C c * B) := by
        rw [show (A + B) * (A + B + C c) = (A + B)^2 + C c*(A+B) by ring,
          CharTwo.add_sq]
        ring
      _ = L + L := by rw [hA, hB]
      _ = 0 := CharTwo.add_self_eq_zero L
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (CharTwo.add_eq_zero.mp h)

/-- Equal values distinguish solutions with the same quadratic equation. -/
theorem artinSchreier_eq_of_eval_eq
    {F : Type*} [Field F] [CharP F 2] (A B L : F[X]) (c β : F)
    (hA : A ^ 2 + C c * A = L) (hB : B ^ 2 + C c * B = L)
    (heval : A.eval β = B.eval β) : A = B := by
  rcases artinSchreier_difference A B L c hA hB with h | h
  · exact CharTwo.add_eq_zero.mp h
  · have hc := congrArg (fun P : F[X] => P.eval β) h
    simp only [eval_add, eval_C, heval, CharTwo.add_self_eq_zero] at hc
    rw [← hc, map_zero] at h
    exact CharTwo.add_eq_zero.mp h

/-- Exterior evaluation distinguishes all solutions, even when the linear
coefficient in the quadratic identity varies with the solution. -/
theorem artinSchreier_eval_injective
    {F : Type*} [Field F] [CharP F 2] (A B L : F[X]) (c d β : F)
    (hA : A ^ 2 + C c * A = L) (hB : B ^ 2 + C d * B = L)
    (hL : L.eval β ≠ 0) (heval : A.eval β = B.eval β) : A = B := by
  have ha := congrArg (fun P : F[X] => P.eval β) hA
  have hb := congrArg (fun P : F[X] => P.eval β) hB
  simp only [eval_add, eval_pow, eval_mul, eval_C] at ha hb
  have ht : B.eval β ≠ 0 := by
    intro ht
    apply hL
    simpa [ht] using hb.symm
  have hcd : c = d := by
    rw [heval] at ha
    exact mul_right_cancel₀ ht (add_left_cancel (ha.trans hb.symm))
  subst d
  rcases artinSchreier_difference A B L c hA hB with h | h
  · exact CharTwo.add_eq_zero.mp h
  · have hc := congrArg (fun P : F[X] => P.eval β) h
    simp only [eval_add, eval_C, heval, CharTwo.add_self_eq_zero] at hc
    rw [← hc, map_zero] at h
    exact CharTwo.add_eq_zero.mp h
/-- An Artin--Schreier solution with zero constant term inherits the
polynomial translation law of its additive right-hand side. -/
theorem artinSchreier_comp_X_add_C
    {F : Type*} [Field F] [CharP F 2] (P L : F[X]) (c : F)
    (hP : P ^ 2 + C c * P = L) (hP0 : P.eval 0 = 0)
    (hL : ∀ y : F, L.comp (X + C y) = L + C (L.eval y)) (y : F) :
    P.comp (X + C y) = P + C (P.eval y) := by
  have hA : (P.comp (X + C y)) ^ 2 + C c * P.comp (X + C y) =
      L + C (L.eval y) := by
    have h := congrArg (fun Q : F[X] => Q.comp (X + C y)) hP
    simpa only [add_comp, pow_comp, mul_comp, C_comp, hL] using h
  have hy : (P.eval y)^2 + c * P.eval y = L.eval y := by
    simpa only [eval_add, eval_pow, eval_mul, eval_C] using
      congrArg (fun Q : F[X] => Q.eval y) hP
  have hB : (P + C (P.eval y)) ^ 2 + C c * (P + C (P.eval y)) =
      L + C (L.eval y) := by
    calc
      _ = (P^2 + C c*P) + C ((P.eval y)^2 + c*P.eval y) := by
        rw [CharTwo.add_sq]
        simp only [map_add, map_mul, map_pow]
        ring
      _ = _ := by rw [hP, hy]
  apply artinSchreier_eq_of_eval_eq _ _ _ c 0 hA hB
  simp [hP0]
end BinaryFieldCounterexamples
