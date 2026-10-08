/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Repairs
public import BinaryFieldCounterexamples.Constructions.Gold.Shape
/-!
# One complete Gold locator witness

A tensor of rank `2t` with the initial Gold moments zero, together with a
linear repair and binary level having the majority zero count, yields the
actual quotient locator. This module assembles its monicity, exact half-domain
degree, exact low tail degree, complementary root count, and recovery
identity. The majority-count input is a finite quadratic-form statement,
separate from the polynomial construction.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The actual Gold locator obtained from a specified tensor, linear repair, and binary level. -/
noncomputable def repairedLocator (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2) (t : ℕ) : B[X] :=
  quotientLocator (normalizingRoot D) (repairedSquareRoot t (repairedPolynomial D v A l κ))
    (subspacePolynomial D) (repairedPolynomial D v A l κ)
/-- A single majority repair gives a monic locator with the exact Gold root count and tail degree. -/
theorem repairedLocator_properties (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-t)) :
    (repairedLocator D v A l κ t).Monic ∧
      (repairedLocator D v A l κ t).natDegree = 2^k ∧
      (repairedLocator D v A l κ t + goldSourcePolynomial D k).natDegree =
        2^(k-1)-2^(k-t-1) ∧
      Nat.card {x : D // (repairedLocator D v A l κ t).eval (x : B)=0} = 2^k-2^(k-t) ∧
      (repairedLocator D v A l κ t).derivative *
        ((repairedLocator D v A l κ t)^2+subspacePolynomial D) =
        C ((subspacePolynomial D).coeff 1)*repairedLocator D v A l κ t := by
  classical
  let H := repairedPolynomial D v A l κ
  let U := repairedSquareRoot t H
  let L := subspacePolynomial D
  let η := normalizingRoot D
  have hdegrees := repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr
  have hHdegree : H.natDegree=2^k+2^(k-t) := hdegrees.1
  have hUdegree : U.natDegree=2^(k-t) := hdegrees.2
  have hH : H ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hHdegree
    have : 0 < (2:ℕ)^k+2^(k-t) := by positivity
    omega
  have hU : U ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hUdegree
    have : 0 < (2:ℕ)^(k-t) := by positivity
    omega
  have hdiv : H ∣ L := (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hU' : U.derivative=0 := repairedSquareRoot_derivative t ht0 H
  have hH' : H.derivative=U^2 := (repairedSquareRoot_sq t (by omega) H
    (repairedPolynomial_derivative_support D k hD v A l κ t hM)).symm
  have hAS : H^2+H=C (η^2)*L*U^2 := by
    rw [show H^2+H=normalizedLocator D*H.derivative from repairedPolynomial_artinSchreier D v A l κ,
      hH', normalizedLocator, ← normalizingRoot_sq]
  have hL : L.Monic := subspacePolynomial_monic D
  have hLdegree : L.natDegree=2^(k+1) := by
    rw [subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hD]
  have hQ : L/H ≠ 0 := by
    intro h
    have he := EuclideanDomain.mul_div_cancel' hH hdiv
    rw [h, mul_zero] at he
    exact hL.ne_zero he.symm
  have hQdegree : (L/H).natDegree=2^k-2^(k-t) := by
    have he := congrArg natDegree (EuclideanDomain.mul_div_cancel' hH hdiv)
    rw [natDegree_mul hH hQ, hHdegree, hLdegree, pow_succ] at he
    omega
  have hQlt : (L/H).degree<L.degree := by
    apply degree_lt_degree
    rw [hQdegree, hLdegree, pow_succ]
    have : 0 < (2:ℕ)^k := by positivity
    omega
  have hη : η ≠ 0 := normalizingRoot_ne_zero D
  have hPloc : repairedLocator D v A l κ t = quotientLocator η U L H := rfl
  refine ⟨quotientLocator_monic η U L H hH hdiv hAS hL hQlt, ?_, ?_, ?_, ?_⟩
  · rw [hPloc, quotientLocator_natDegree η U L H hH hdiv hAS hQlt, hLdegree, pow_succ,
      Nat.mul_div_cancel _ (by decide : 0 < 2)]
  · have hsmall : 2^(k-t)<2^(k-1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have hhalf : 2^k=2^(k-1)*2 := by rw [← pow_succ]; congr 1; omega
    have htail := gold_locator_tail_natDegree D k (by omega) hD
      (quotientLocator η U L H) (L/H) (quotientLocator_sq η U L H hH hdiv hAS)
      (by rw [hQdegree, hhalf]; omega)
    rw [hPloc, htail, hQdegree]
    have hunit : 2^(k-t)=2^(k-t-1)*2 := by rw [← pow_succ]; congr 1; omega
    rw [hhalf, hunit]
    omega
  · have he : Nat.card {x : D // (repairedLocator D v A l κ t).eval (x : B)=0} =
        Nat.card {x : D // ¬(tensorQuadraticFunction D v A x+l x+κ=0)} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      rw [hPloc, quotientLocator_eval_eq_zero_iff η U L H hH hdiv hAS (x : B)
        ((subspacePolynomial_eval_eq_zero_iff D (x : B)).mpr x.property)]
      change (repairedPolynomial D v A l κ).eval (x : B) ≠ 0 ↔ _
      rw [repairedPolynomial_eval, _root_.map_ne_zero]
    rw [he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hzeros, hD, pow_succ]
    omega
  · have he := quotientLocator_recovery η U L H hη hU hH hdiv hAS hH' hU'
    simpa only [η, normalizingRoot_sq, inv_inv, hPloc] using he
end BinaryFieldCounterexamples.Gold
