/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Strict-degree witnesses obtained by removing a zero constant term

The locator constructions first give a numerator of degree at most the message
bound. Dividing by `X` gives the required strict degree, including a zero
numerator, while preserving evaluation identities away from zero.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Dividing by `X` converts a non-strict natural-degree bound into a strict
polynomial-degree bound. This includes the zero polynomial and `K = 0`. -/
theorem degree_divX_lt_of_natDegree_le
    {F : Type*} [Field F] (P : F[X]) (K : ℕ) (hP : P.natDegree ≤ K) :
    P.divX.degree < K := by
  by_cases hz : P = 0
  · simp [hz]
  exact (degree_divX_lt hz).trans_le (degree_le_of_natDegree_le hP)

/-- At a zero-constant numerator, multiplication by the coordinate undoes `divX`. -/
theorem eval_divX_mul_of_coeff_zero
    {F : Type*} [Field F] (P : F[X]) (hP : P.coeff 0 = 0) (x : F) :
    P.divX.eval x * x = P.eval x := by
  have h := congrArg (fun Q : F[X] ↦ Q.eval x) (divX_mul_X_add P)
  simpa [hP] using h

/-- An equality to a positive monomial descends after removing `X` at a nonzero coordinate. -/
theorem eval_divX_eq_pow_pred
    {F : Type*} [Field F] (P : F[X]) (hP : P.coeff 0 = 0)
    (x : F) (hx : x ≠ 0) (n : ℕ) (hn : 0 < n) (heval : P.eval x = x ^ n) :
    P.divX.eval x = x ^ (n - 1) := by
  apply mul_right_cancel₀ hx
  rw [eval_divX_mul_of_coeff_zero P hP x, heval, ← pow_succ]
  congr 1
  omega

end BinaryFieldCounterexamples
