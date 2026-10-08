/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.Algebra.Polynomial.FieldDivision
/-!
# Divisibility reflected by nonconstant polynomial composition

Over a field, composition with a nonconstant polynomial preserves nonzero
polynomials and reflects divisibility. The latter follows by Euclidean division:
a nonzero composed remainder has degree strictly below the composed divisor.
This transfers the quadratic derivative factorization to a descended polynomial.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
variable {K : Type*} [Field K]
/-- Nonconstant composition preserves nonzero polynomials. -/
theorem polynomial_comp_ne_zero (A P : K[X]) (hA : A.natDegree ≠ 0) (hP : P ≠ 0) :
    P.comp A ≠ 0 := by
  intro h
  rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
  · exact hP h
  · exact hA (by rw [h, natDegree_C])

/-- Divisibility is equivalent before and after nonconstant composition. -/
theorem polynomial_comp_dvd_iff (A P Q : K[X]) (hA : A.natDegree ≠ 0) :
    P.comp A ∣ Q.comp A ↔ P ∣ Q := by
  constructor
  · intro hd
    by_cases hp : P = 0
    · subst P
      simp only [zero_comp, zero_dvd_iff] at hd ⊢
      by_contra hq
      exact polynomial_comp_ne_zero A Q hA hq hd
    by_cases hpd : P.natDegree = 0
    · have hu : IsUnit P := by
        rw [eq_C_of_natDegree_eq_zero hpd]
        apply isUnit_C.mpr
        apply isUnit_iff_ne_zero.mpr
        intro hz
        apply hp
        rw [eq_C_of_natDegree_eq_zero hpd, hz, C_0]
      exact hu.dvd
    apply EuclideanDomain.mod_eq_zero.mp
    by_contra hrem
    have he : (Q % P).comp A = Q.comp A - (P.comp A) * ((Q / P).comp A) := by
      have hh := EuclideanDomain.mod_add_div Q P
      have hc := congrArg (fun S : K[X] => S.comp A) hh
      simp only [add_comp, mul_comp] at hc
      exact eq_sub_of_add_eq hc
    have hdrem : P.comp A ∣ (Q % P).comp A := by
      rw [he]
      exact dvd_sub hd (dvd_mul_right _ _)
    have hle := natDegree_le_of_dvd hdrem (polynomial_comp_ne_zero A _ hA hrem)
    rw [natDegree_comp, natDegree_comp] at hle
    have hlt := Nat.mul_lt_mul_of_pos_right (natDegree_mod_lt Q hpd) (Nat.pos_of_ne_zero hA)
    omega
  · rintro ⟨T, rfl⟩
    rw [mul_comp]
    exact dvd_mul_right _ _
end BinaryFieldCounterexamples
