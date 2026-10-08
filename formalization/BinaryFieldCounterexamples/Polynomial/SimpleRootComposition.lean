/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.Algebra.Polynomial.FieldDivision
/-!
# Multiplicity under composition at a simple zero

Composition through a polynomial with a simple zero at the origin preserves
the outer polynomial's multiplicity there. Consequently it preserves the exact
powers of X which divide the polynomial. This recovers lower support bounds
when descending through the hyperplane map, whose derivative is one.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
variable {K : Type*} [Field K]
/-- Root multiplicities scale by the exponent of a nonzero polynomial power. -/
theorem rootMultiplicity_pow_at (A : K[X]) (hA : A ≠ 0) (x : K) (r : ℕ) :
    (A^r).rootMultiplicity x = r * A.rootMultiplicity x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hA) hA), ih]
    ring

/-- Composition at a simple zero preserves the outer multiplicity at zero. -/
theorem rootMultiplicity_comp_simple_zero (A H : K[X])
    (hzero : A.eval 0 = 0) (hderiv : A.derivative.eval 0 ≠ 0) :
    (H.comp A).rootMultiplicity 0 = H.rootMultiplicity 0 := by
  have hA : A ≠ 0 := by intro h; simp [h] at hderiv
  have hdeg : A.natDegree ≠ 0 := by
    intro h
    have he := eq_C_of_natDegree_eq_zero h
    rw [he, derivative_C, eval_zero] at hderiv
    exact hderiv rfl
  have hmult : A.rootMultiplicity 0 = 1 := by
    have hp := (rootMultiplicity_pos (p := A) (x := 0) hA).mpr hzero
    have hn : ¬ 1 < A.rootMultiplicity 0 := by
      rw [one_lt_rootMultiplicity_iff_isRoot hA]
      exact fun h => hderiv h.2
    omega
  by_cases hH : H = 0
  · simp [hH]
  have hc : H.comp A ≠ 0 := by
    intro hz
    rcases comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
    · exact hH h
    · exact hdeg (by rw [h, natDegree_C])
  obtain ⟨T, he, ht⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd H hH 0
  have ht0 : T.eval 0 ≠ 0 := by
    simpa only [dvd_iff_isRoot, IsRoot.def] using ht
  have htc : (T.comp A).rootMultiplicity 0 = 0 :=
    rootMultiplicity_eq_zero (by simpa only [IsRoot.def, eval_comp, hzero] using ht0)
  have hec : H.comp A = A^H.rootMultiplicity 0 * T.comp A := by
    conv_lhs => rw [he]
    simp only [mul_comp, pow_comp, X_comp, map_zero, sub_zero]
  rw [hec, rootMultiplicity_mul (hec ▸ hc), rootMultiplicity_pow_at A hA,
    hmult, htc, mul_one, add_zero]
/-- Divisibility by any power of X is equivalent before and after composition at a simple zero. -/
theorem X_pow_dvd_comp_simple_zero (A H : K[X])
    (hzero : A.eval 0 = 0) (hderiv : A.derivative.eval 0 ≠ 0) (n : ℕ) :
    X^n ∣ H.comp A ↔ X^n ∣ H := by
  by_cases hH : H = 0
  · simp [hH]
  have hc : H.comp A ≠ 0 := by
    intro hz
    rcases comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
    · exact hH h
    · rw [h, derivative_C, eval_zero] at hderiv
      exact hderiv rfl
  have he := rootMultiplicity_comp_simple_zero A H hzero hderiv
  have hl := le_rootMultiplicity_iff hc (a := 0) (n := n)
  have hr := le_rootMultiplicity_iff hH (a := 0) (n := n)
  rw [he] at hl
  simpa only [map_zero, sub_zero] using hl.symm.trans hr
end BinaryFieldCounterexamples
