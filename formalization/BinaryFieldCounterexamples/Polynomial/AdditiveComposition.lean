/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Inner polynomials of additive compositions

This module proves the full arbitrary-field assertion of the paper's
[Lemma 3.10, p. 22](../../../binary-field-counterexamples.pdf#page=22)
(`lem:additive-composition` in `sections/preliminaries.tex`): if `L = A.comp P`,
`L` and `A` are additive, `A ≠ 0`, and `P.eval 0 = 0`, then `P` is additive
and its roots form an additive subgroup.

Additivity here means the literal bivariate polynomial identity, encoded in
`F[X][X]`, rather than just an identity of evaluations on `F`. A substitution
lemma transports that identity to any commutative ring. Applying the nonzero
outer polynomial to the additive defect makes it zero. Composition degree
forces the defect to be constant in the outer variable, and evaluating that
variable at zero then forces the defect itself to vanish.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Literal polynomial additivity. The outer `X` and the inner `C X` are the
two independent variables, and the right side is `P(X) + P(Y)`. -/
def IsAdditivePolynomial {F : Type*} [CommRing F] (P : F[X]) : Prop :=
  (P.map C).comp (X + C X) = P.map C + C P

/-- Substituting arbitrary elements into the bivariate identity gives
additivity of evaluation through any ring homomorphism. -/
theorem IsAdditivePolynomial.eval2_add
    {F S : Type*} [CommRing F] [CommRing S] {P : F[X]}
    (hP : IsAdditivePolynomial P) (f : F →+* S) (x y : S) :
    P.eval₂ f (x + y) = P.eval₂ f x + P.eval₂ f y := by
  change (P.map C).comp (X + C X) = P.map C + C P at hP
  have h := congrArg (fun Q : F[X][X] => Q.eval₂ (eval₂RingHom f y) x) hP
  simpa only [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_map, Polynomial.eval₂RingHom_comp_C,
    Polynomial.coe_eval₂RingHom] using h

/-- An additive polynomial has zero constant term. -/
theorem IsAdditivePolynomial.eval2_zero
    {F S : Type*} [CommRing F] [CommRing S] {P : F[X]}
    (hP : IsAdditivePolynomial P) (f : F →+* S) : P.eval₂ f 0 = 0 := by
  have h := hP.eval2_add f 0 0
  simpa only [zero_add, add_eq_left] using h.symm

/-- Polynomial additivity also transports subtraction. -/
theorem IsAdditivePolynomial.eval2_sub
    {F S : Type*} [CommRing F] [CommRing S] {P : F[X]}
    (hP : IsAdditivePolynomial P) (f : F →+* S) (x y : S) :
    P.eval₂ f (x - y) = P.eval₂ f x - P.eval₂ f y := by
  have h := hP.eval2_add f (x - y) y
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- The full inner-polynomial clause of `lem:additive-composition`: normalized
right factors of nonzero additive polynomials are polynomial-additive.
No restriction on the characteristic or on the degree of `A` is imposed. -/
theorem isAdditivePolynomial_of_comp
    {F : Type*} [Field F] (L A P : F[X])
    (hcomp : L = A.comp P) (hL : IsAdditivePolynomial L)
    (hA : IsAdditivePolynomial A) (hAne : A ≠ 0) (hP0 : P.eval 0 = 0) :
    IsAdditivePolynomial P := by
  let f : F →+* F[X][X] := C.comp C
  let R : F[X][X] := P.eval₂ f (X + C X) - P.eval₂ f X - P.eval₂ f (C X)

  have hAR : A.eval₂ f R = 0 := by
    dsimp only [R]
    rw [hA.eval2_sub, hA.eval2_sub]
    simp only [← eval₂_comp, ← hcomp]
    rw [hL.eval2_add]
    ring
  have hARcomp : (A.map C).comp R = 0 := by
    simpa only [comp, eval₂_map, f] using hAR
  have hAmap : A.map C ≠ 0 := by
    intro h
    apply hAne
    exact (map_injective C C_injective) (by simpa using h)
  have hRconstant : R = C (R.coeff 0) :=
    ((comp_eq_zero_iff.mp hARcomp).resolve_left hAmap).2

  have hR0 : R.eval 0 = 0 := by
    change (evalRingHom 0) R = 0
    simp only [R, map_sub, hom_eval₂, f, coe_evalRingHom,
      eval_add, eval_X, eval_C, zero_add]
    simp [eval₂_at_zero, coeff_zero_eq_eval_zero, hP0]
  have hR : R = 0 := by
    rw [hRconstant]
    simp only [coeff_zero_eq_eval_zero, hR0, C_0]

  unfold IsAdditivePolynomial
  have hx : P.eval₂ f X = P.map C := by
    rw [show f = C.comp C from rfl, ← eval₂_map, eval₂_C_X]
  have hy : P.eval₂ f (C X) = C P := by
    rw [show f = C.comp C from rfl, ← eval₂_map]
    change (P.map C).comp (C X) = C P
    rw [comp_C, eval_map, eval₂_C_X]
  have hdefect : (P.map C).comp (X + C X) - P.map C - C P = 0 := by
    rw [comp, eval₂_map]
    simpa only [R, hx, hy] using hR
  simpa only [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hdefect)

/-- The roots-subgroup clause of `lem:additive-composition`, packaged as an
additive subgroup whose membership is exactly the root condition. -/
theorem exists_rootAddSubgroup_of_additive_comp
    {F : Type*} [Field F] (L A P : F[X])
    (hcomp : L = A.comp P) (hL : IsAdditivePolynomial L)
    (hA : IsAdditivePolynomial A) (hAne : A ≠ 0) (hP0 : P.eval 0 = 0) :
    ∃ W : AddSubgroup F, ∀ x : F, x ∈ W ↔ P.eval x = 0 := by
  have hP := isAdditivePolynomial_of_comp L A P hcomp hL hA hAne hP0
  let g : F →+ F :=
    { toFun := P.eval
      map_zero' := hP0
      map_add' := fun x y => hP.eval2_add (RingHom.id F) x y }
  exact ⟨g.ker, fun _ => Iff.rfl⟩

end BinaryFieldCounterexamples
