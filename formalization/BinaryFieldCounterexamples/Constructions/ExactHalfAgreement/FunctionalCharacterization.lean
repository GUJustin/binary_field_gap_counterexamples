/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.Parameters
public import BinaryFieldCounterexamples.Polynomial.ArtinSchreier

/-!
# Recovering affine binary functionals from polynomial identities

An Artin--Schreier identity over the prescribed domain locator produces an actual
binary-valued additive functional. Strict-degree interpolation identifies its
canonical polynomial, including its values outside the domain. The affine variant
recovers the two fiber values and nonzero scaling used by exact-half locators.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- A zero-constant quadratic solution over the domain locator is the canonical
polynomial of an actual binary functional. -/
theorem exists_functional_of_artinSchreier
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (P : F[X]) (t : F)
    (hP0 : P.eval 0 = 0)
    (hdeg : P.degree < (Nat.card D : WithBot ℕ))
    (hAS : P ^ 2 + P = C t * subspacePolynomial D) :
    ∃ l : D →+ ZMod 2, P = Gold.functionalPolynomial D l := by
  classical
  have hcomp : ∀ y : F, P.comp (X+C y) = P+C (P.eval y) := by
    apply artinSchreier_comp_X_add_C P (C t * subspacePolynomial D) 1
    · simpa using hAS
    · exact hP0
    · intro y
      simp only [mul_comp, C_comp, subspacePolynomial_comp_X_add_C,
        eval_mul, eval_C, map_mul]
      ring
  have hadd (x y : F) : P.eval (x+y) = P.eval (x : F) + P.eval y := by
    simpa using congrArg (fun Q : F[X] => Q.eval (x : F)) (hcomp y)
  have hrange (x : D) : ∃ b : ZMod 2, algebraMap (ZMod 2) F b = P.eval (x : F) := by
    have h := congrArg (fun Q : F[X] => Q.eval (x : F)) hAS
    simp only [eval_add, eval_pow, eval_mul, eval_C,
      (subspacePolynomial_eval_eq_zero_iff D (x : F)).mpr x.property, mul_zero] at h
    have hf : P.eval (x : F) * (P.eval (x : F) + 1) = 0 := by simpa only [mul_add, mul_one, ← pow_two] using h
    rcases mul_eq_zero.mp hf with hz | hz
    · exact ⟨0, by simpa using hz.symm⟩
    · exact ⟨1, by simpa using (CharTwo.add_eq_zero.mp hz).symm⟩
  let l : D →+ ZMod 2 :=
    { toFun := fun x => (hrange x).choose
      map_zero' := by
        apply (algebraMap (ZMod 2) F).injective
        simpa only [map_zero, AddSubgroup.coe_zero, hP0] using (hrange 0).choose_spec
      map_add' := by
        intro x y
        apply (algebraMap (ZMod 2) F).injective
        simpa only [map_add, (hrange (x+y)).choose_spec, (hrange x).choose_spec,
          (hrange y).choose_spec, AddSubgroup.coe_add] using hadd x y }
  refine ⟨l, Gold.eq_functionalPolynomial D l P hdeg ?_⟩
  intro x
  exact (hrange x).choose_spec.symm
/-- Every affine quadratic solution is a scaled canonical binary functional
plus one of its two fiber values. -/
theorem exists_functional_of_affine_artinSchreier
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (A : F[X]) (c : F) (hc : c ≠ 0)
    (hdeg : A.degree < (Nat.card D : WithBot ℕ))
    (hAS : A ^ 2 + C c * A = subspacePolynomial D) :
    ∃ (l : D →+ ZMod 2) (b : ZMod 2),
      A = C c * (Gold.functionalPolynomial D l + C (algebraMap (ZMod 2) F b)) := by
  let B := C c⁻¹ * A
  have hi : C c⁻¹ * C c = (1 : F[X]) := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have hB : B^2+B = C (c⁻¹^2) * subspacePolynomial D := by
    rw [← hAS, map_pow]
    dsimp [B]
    calc
      _ = (C c⁻¹)^2 * A^2 + (C c⁻¹)*(C c⁻¹*C c)*A := by rw [hi]; ring
      _ = _ := by ring
  have hB0 : (B.eval 0)^2 + B.eval 0 = 0 := by
    simpa [← coeff_zero_eq_eval_zero] using congrArg (fun Q : F[X] => Q.eval 0) hB
  have hb : ∃ b : ZMod 2, algebraMap (ZMod 2) F b = B.eval 0 := by
    have h : B.eval 0 * (B.eval 0 + 1) = 0 := by
      simpa only [mul_add, mul_one, ← pow_two] using hB0
    rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using (CharTwo.add_eq_zero.mp h).symm⟩
  obtain ⟨b, hb⟩ := hb
  let P := B + C (B.eval 0)
  have hP0 : P.eval 0 = 0 := by simp [P, CharTwo.add_self_eq_zero]
  have hPdeg : P.degree < (Nat.card D : WithBot ℕ) := by
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · dsimp [B]
      rw [degree_C_mul (inv_ne_zero hc)]
      exact hdeg
    · apply degree_C_le.trans_lt
      exact_mod_cast Nat.card_pos (α := D)
  have hP : P^2+P = C (c⁻¹^2)*subspacePolynomial D := by
    calc
      _ = (B^2+B) + C ((B.eval 0)^2+B.eval 0) := by
        dsimp [P]
        rw [CharTwo.add_sq]
        simp only [map_add, map_pow]
        ring
      _ = _ := by rw [hB, hB0, C_0, add_zero]
  obtain ⟨l, hl⟩ := exists_functional_of_artinSchreier D P (c⁻¹^2) hP0 hPdeg hP
  refine ⟨l, b, ?_⟩
  rw [← hl, hb]
  have hcancel : P+C (B.eval 0) = B := by
    dsimp [P]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hcancel]
  dsimp [B]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
end BinaryFieldCounterexamples
