/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.AdditiveComposition
public import BinaryFieldCounterexamples.Polynomial.AffineFlatLocators
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound

/-!
# Binary additivity and affine-flat squares

This module proves the literal polynomial-additivity claim in the locator prose
of Section 3 (`sections/preliminaries.tex`, lines 235–241) and instantiates it
for actual subspace locators. It also supplies the nonzero constant derivative
and square-root degree clauses for actual affine-flat locators.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial BinaryLocator
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 3's locator prose: binary linearized polynomials satisfy the
literal bivariate polynomial identity `L(X+Y) = L(X)+L(Y)`. -/
theorem BinaryLocator.IsBinaryLinearized.isAdditivePolynomial
    {F : Type*} [Field F] [CharP F 2] {P : F[X]}
    (hP : IsBinaryLinearized P) : IsAdditivePolynomial P := by
  classical
  have hsum : P = ∑ n ∈ P.support, C (P.coeff n) * X ^ n := by
    simpa only [Polynomial.sum] using (sum_C_mul_X_pow_eq P).symm
  unfold IsAdditivePolynomial
  rw [hsum]
  simp only [Polynomial.map_sum, sum_comp, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨i, rfl⟩ := hP n hn
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, mul_comp, C_comp, pow_comp, X_comp, C_mul, C_pow]
  rw [add_pow_char_pow]
  rw [mul_add]

/-- Section 3's locator prose, and the locator instance needed for Lemma 3.10:
the actual product locator of every finite binary subspace is additive as a
polynomial identity, even when the ambient field is infinite. -/
theorem subspacePolynomial_isAdditivePolynomial
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] :
    IsAdditivePolynomial (subspacePolynomial W) := by
  exact BinaryLocator.IsBinaryLinearized.isAdditivePolynomial (subspacePolynomial_support W)

/-- Lemma 3.10 instantiated on an actual binary subspace locator: a normalized
inner factor of a nonzero additive outer factor is additive and has an
additive subgroup as its exact root set. -/
theorem subspacePolynomial_additive_composition_inner
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (A P : F[X])
    (hcomp : subspacePolynomial W = A.comp P)
    (hA : IsAdditivePolynomial A) (hAne : A ≠ 0) (hP0 : P.eval 0 = 0) :
    IsAdditivePolynomial P ∧ ∃ U : AddSubgroup F, ∀ x : F, x ∈ U ↔ P.eval x = 0 := by
  have hL := subspacePolynomial_isAdditivePolynomial W
  exact ⟨isAdditivePolynomial_of_comp _ A P hcomp hL hA hAne hP0,
    exists_rootAddSubgroup_of_additive_comp _ A P hcomp hL hA hAne hP0⟩

/-- Section 3's locator prose: the locator of the translate `a + A.direction`
differs from the direction-space locator only by a constant. If `a ∈ A`,
this is the locator of `A` itself. -/
theorem affineFlatLocator_eq_subspacePolynomial_add_constant
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) :
    affineFlatLocator A a = subspacePolynomial A.direction.toAddSubgroup +
      C ((subspacePolynomial A.direction.toAddSubgroup).eval a) := by
  unfold affineFlatLocator
  rw [CharTwo.sub_eq_add, subspacePolynomial_comp_X_add_C]

/-- Section 3's locator prose: an affine-flat locator has constant derivative,
namely the nonzero linear coefficient of the direction-space locator. -/
theorem affineFlatLocator_derivative_constant
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) :
    (affineFlatLocator A a).derivative =
      C ((subspacePolynomial A.direction.toAddSubgroup).coeff 1) ∧
      (subspacePolynomial A.direction.toAddSubgroup).coeff 1 ≠ 0 := by
  refine ⟨?_, subspacePolynomial_coeff_one_ne_zero _⟩
  rw [affineFlatLocator_eq_subspacePolynomial_add_constant, derivative_add,
    derivative_C, add_zero]
  apply derivative_eq_C_of_binaryAffineSupport
  intro n hn
  exact Or.inr (subspacePolynomial_support _ n hn)

/-- Section 3's locator prose: adding the derivative term `cX` to the locator
of `a + A.direction`, whose direction has size `2^(m+1)`, gives a square of
degree exactly `2^m`. The constant `c` is nonzero and is the derivative.
The next theorem identifies this translate with the actual flat `A`. -/
theorem affineFlatLocator_add_linear_exists_square
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) (m : ℕ)
    (hcard : Nat.card A.direction = 2 ^ (m + 1)) :
    ∃ c : F, c ≠ 0 ∧ (affineFlatLocator A a).derivative = C c ∧
      ∃ Q : F[X], Q.natDegree = 2 ^ m ∧
        Q ^ 2 = affineFlatLocator A a + C c * X := by
  let W := A.direction.toAddSubgroup
  let c := (subspacePolynomial W).coeff 1
  let P := affineFlatLocator A a + C c * X
  have heven : ∀ n ∈ P.support, Even n := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have hcoeff : P.coeff n ≠ 0 := mem_support_iff.mp hn
    have hshape : P = binaryQuarterRadicand W 0 +
        C ((subspacePolynomial W).eval a) := by
      simp only [P, affineFlatLocator_eq_subspacePolynomial_add_constant,
        binaryQuarterRadicand, C_0, sub_zero, c, W]
      rw [CharTwo.sub_eq_add]
      ring
    have hr : (binaryQuarterRadicand W 0).coeff n ≠ 0 := by
      simpa only [hshape, coeff_add, coeff_C, ite_eq_right hn0, add_zero] using hcoeff
    exact binaryQuarterRadicand_even_support W 0 n (mem_support_iff.mpr hr)
  have hdegree : P.natDegree = 2 ^ (m + 1) := by
    have hsmall : (C c * X : F[X]).natDegree < (affineFlatLocator A a).natDegree := by
      apply lt_of_le_of_lt (natDegree_C_mul_le c X)
      rw [natDegree_X, affineFlatLocator_natDegree, hcard]
      exact Nat.one_lt_pow (by omega) (by omega)
    dsimp only [P]
    rw [natDegree_add_eq_left_of_natDegree_lt hsmall,
      affineFlatLocator_natDegree, hcard]
  let Q := evenPolynomialSquareRoot P
  have hsq : Q ^ 2 = P := evenPolynomialSquareRoot_sq P heven
  have hQdegree : Q.natDegree = 2 ^ m := by
    have h := congrArg natDegree hsq
    rw [natDegree_pow, hdegree, pow_succ] at h
    omega
  refine ⟨c, (affineFlatLocator_derivative_constant A a).2,
    (affineFlatLocator_derivative_constant A a).1, Q, hQdegree, hsq⟩

/-- Section 3's affine-flat locator prose, assembled on the actual flat `A`:
when `a ∈ A` and `|A| = 2^(m+1)`, its locator has precisely the roots `A`,
has nonzero constant derivative `c`, and becomes a square of degree `2^m`
after adding `cX`. -/
theorem affineFlatLocator_square_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) (ha : a ∈ A) (m : ℕ)
    (hcard : Nat.card A = 2 ^ (m + 1)) :
    (∀ x : F, (affineFlatLocator A a).eval x = 0 ↔ x ∈ A) ∧
      ∃ c : F, c ≠ 0 ∧ (affineFlatLocator A a).derivative = C c ∧
        ∃ Q : F[X], Q.natDegree = 2 ^ m ∧
          Q ^ 2 = affineFlatLocator A a + C c * X := by
  let e : A.direction ≃ A :=
    { toFun := fun v => ⟨(v : F) + a, by
        apply (AffineSubspace.vsub_right_mem_direction_iff_mem ha _).mp
        change (v : F) + a - a ∈ A.direction
        simpa only [add_sub_cancel_right] using v.property⟩
      invFun := fun x => ⟨(x : F) - a,
        (AffineSubspace.vsub_right_mem_direction_iff_mem ha (x : F)).mpr x.property⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  have hdirection : Nat.card A.direction = 2 ^ (m + 1) :=
    (Nat.card_congr e).trans hcard
  exact ⟨fun x => affineFlatLocator_eval_eq_zero_iff A a ha x,
    affineFlatLocator_add_linear_exists_square A a m hdirection⟩

end BinaryFieldCounterexamples
