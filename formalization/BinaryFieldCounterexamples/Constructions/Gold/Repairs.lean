/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Saturation
/-!
# Literal linear repairs and the discarded Gold factor

A repair adds the canonical polynomial of a binary functional and a binary
constant to the tensor polynomial. The resulting polynomial still satisfies
the differential Artin--Schreier equation. Moment and rank hypotheses give
its exact degree and a concrete square-root derivative with zero derivative.
The majority root count, supplied separately by finite quadratic-form
counting, then proves that this actual polynomial is a separable divisor of
the prescribed domain's product locator.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The literal binary quadratic function represented by a tensor polynomial. -/
noncomputable def tensorQuadraticFunction (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (x : D) : ZMod 2 :=
  ∑ ij : TensorIndex d, A ij *
    (((parameterEquiv D).symm (v ij.val.1)) x * ((parameterEquiv D).symm (v ij.val.2)) x)
/-- The quadratic function vanishes at the origin. -/
theorem tensorQuadraticFunction_zero (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    tensorQuadraticFunction D v A 0 = 0 := by
  simp [tensorQuadraticFunction]
/-- The binary quadratic function has exactly the concrete tensor polar map. -/
theorem tensorQuadraticFunction_add (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (x y : D) :
    tensorQuadraticFunction D v A (x+y) = tensorQuadraticFunction D v A x +
      tensorQuadraticFunction D v A y + tensorPolarMap D v A y x := by
  apply (algebraMap (ZMod 2) B).injective
  have he := tensorPolynomial_polar_eval D v A y x
  simp only [tensorPolynomial_eval] at he
  change algebraMap (ZMod 2) B (tensorQuadraticFunction D v A (x+y)) +
    algebraMap (ZMod 2) B (tensorQuadraticFunction D v A x) +
    algebraMap (ZMod 2) B (tensorQuadraticFunction D v A y) =
      algebraMap (ZMod 2) B ((tensorPolarFunctional D v A y) x) at he
  simp only [map_add]
  change _ = _ + _ + algebraMap (ZMod 2) B ((tensorPolarFunctional D v A y) x)
  rw [← he]
  linear_combination (norm := ring_nf)
    -(algebraMap (ZMod 2) B (tensorQuadraticFunction D v A x) +
      algebraMap (ZMod 2) B (tensorQuadraticFunction D v A y)) * (CharTwo.two_eq_zero (R := B))
/-- Add a binary linear repair and then choose one of the two binary level sets. -/
noncomputable def repairedPolynomial (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2) : B[X] :=
  tensorPolynomial D v A + functionalPolynomial D l + C (algebraMap (ZMod 2) B κ)
/-- The repaired polynomial interpolates the actual repaired binary quadratic function. -/
theorem repairedPolynomial_eval (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2) (x : D) :
    (repairedPolynomial D v A l κ).eval (x : B) =
      algebraMap (ZMod 2) B (tensorQuadraticFunction D v A x + l x + κ) := by
  simp only [repairedPolynomial, tensorQuadraticFunction, eval_add, eval_C, tensorPolynomial_eval,
    functionalPolynomial_eval, map_add]
/-- Linear repair and binary translation preserve the exact differential Artin--Schreier equation. -/
theorem repairedPolynomial_artinSchreier (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2) :
    repairedPolynomial D v A l κ ^ 2 + repairedPolynomial D v A l κ =
      normalizedLocator D * (repairedPolynomial D v A l κ).derivative := by
  have hl : (functionalPolynomial D l)^2+functionalPolynomial D l =
      normalizedLocator D * (functionalPolynomial D l).derivative := by
    rw [derivative_eq_C_of_binarySupport _ (functionalPolynomial_support_and_degree D l).1, mul_comm]
    exact functionalPolynomial_artinSchreier D l
  have hc : C (algebraMap (ZMod 2) B κ)^2+C (algebraMap (ZMod 2) B κ) =
      normalizedLocator D * (C (algebraMap (ZMod 2) B κ)).derivative := by
    rw [← map_pow, binaryScalar_sq, CharTwo.add_self_eq_zero, derivative_C, mul_zero]
  exact artinSchreier_add _ _ _
    (artinSchreier_add _ _ _ (tensorPolynomial_artinSchreier D v A) hl) hc
/-- Repair changes only the constant part of the tensor derivative. -/
theorem repairedPolynomial_derivative (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2) :
    (repairedPolynomial D v A l κ).derivative = tensorLinearPart D v A +
      C ((∑ ij : TensorIndex d, algebraMap (ZMod 2) B (A ij) *
        ((v ij.val.1 : B)*(v ij.val.2 : B))) + (functionalPolynomial D l).coeff 1) := by
  simp only [repairedPolynomial, derivative_C, add_zero, tensorPolynomial_derivative,
    derivative_eq_C_of_binarySupport _ (functionalPolynomial_support_and_degree D l).1, map_add,
    add_assoc]
/-- The repaired derivative still has Frobenius-divisible support; its constant is harmless. -/
theorem repairedPolynomial_derivative_support (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) :
    ∀ n ∈ (repairedPolynomial D v A l κ).derivative.support, 2^t ∣ n := by
  intro n hn
  by_cases hz : n=0
  · subst n; exact dvd_zero _
  have hc := mem_support_iff.mp hn
  rw [repairedPolynomial_derivative, coeff_add, coeff_C, ite_eq_right (by exact hz), add_zero] at hc
  obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D k hD v A t hM n
    (mem_support_iff.mpr hc)
  exact pow_dvd_pow 2 hi
/-- A concrete square root of a repaired derivative with divisible support. -/
noncomputable def repairedSquareRoot (t : ℕ) (H : B[X]) : B[X] :=
  frobeniusRoot t H.derivative ^ (2^(t-1))
/-- The concrete root squares to the formal derivative. -/
theorem repairedSquareRoot_sq {B : Type*} [Field B] [Fintype B] [CharP B 2] (t : ℕ) (ht : 1 ≤ t) (H : B[X])
    (hsupport : ∀ n ∈ H.derivative.support, 2^t ∣ n) :
    repairedSquareRoot t H ^ 2 = H.derivative := by
  rw [repairedSquareRoot, ← pow_mul, ← pow_succ]
  have he : t-1+1=t := by omega
  rw [he, frobeniusRoot_pow t H.derivative hsupport]
/-- At Gold order at least two, the square root has identically zero formal derivative. -/
theorem repairedSquareRoot_derivative {B : Type*} [Field B] [Fintype B] [CharP B 2] (t : ℕ) (ht : 2 ≤ t) (H : B[X]) :
    (repairedSquareRoot t H).derivative = 0 := by
  unfold repairedSquareRoot
  have he : t-1=(t-2)+1 := by omega
  rw [he, pow_succ, pow_mul, derivative_pow]
  simp [CharTwo.two_eq_zero]
/-- Rank saturation fixes the exact degree of the repaired derivative. -/
theorem repairedPolynomial_derivative_natDegree (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    (repairedPolynomial D v A l κ).derivative.natDegree = 2^(k+1-t) := by
  rw [repairedPolynomial_derivative, natDegree_add_C]
  exact (tensorLinearPart_endpoint_coefficients D k hD v A t ht0 ht hM hr).2.1

/-- A nonconstant Artin--Schreier solution has the exact degree balance forced by its derivative. -/
theorem artinSchreier_degree_balance {B : Type*} [Field B] (H Λ : B[X])
    (hΛ : Λ ≠ 0) (hH' : H.derivative ≠ 0) (hAS : H^2+H=Λ*H.derivative) :
    2*H.natDegree = Λ.natDegree+H.derivative.natDegree := by
  have hn : 0 < H.natDegree := by
    by_contra h
    exact hH' (derivative_of_natDegree_zero (by omega))
  have he := congrArg natDegree hAS
  rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_pow]; omega),
    natDegree_pow, natDegree_mul hΛ hH'] at he
  exact he
/-- The repaired polynomial and its square-root derivative have the exact Gold degrees. -/
theorem repairedPolynomial_natDegrees (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    (repairedPolynomial D v A l κ).natDegree = 2^k+2^(k-t) ∧
      (repairedSquareRoot t (repairedPolynomial D v A l κ)).natDegree = 2^(k-t) := by
  have hderiv := repairedPolynomial_derivative_natDegree D k hD v A l κ t (by omega) ht hM hr
  have hderivne : (repairedPolynomial D v A l κ).derivative ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hderiv
    have : 0 < (2:ℕ)^(k+1-t) := by positivity
    omega
  have hΛne : normalizedLocator D ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D)))
      (subspacePolynomial_monic D).ne_zero
  have hΛdegree : (normalizedLocator D).natDegree = 2^(k+1) := by
    rw [normalizedLocator, natDegree_C_mul (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D)),
      subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hD]
  have hbalance := artinSchreier_degree_balance _ _ hΛne hderivne
    (repairedPolynomial_artinSchreier D v A l κ)
  rw [hΛdegree, hderiv, pow_succ] at hbalance
  have he : k+1-t = (k-t)+1 := by omega
  rw [he, pow_succ] at hbalance
  have hsq := congrArg natDegree (repairedSquareRoot_sq t (by omega) (repairedPolynomial D v A l κ)
    (repairedPolynomial_derivative_support D k hD v A l κ t hM))
  rw [natDegree_pow, hderiv, he, pow_succ] at hsq
  constructor <;> omega

/-- A polynomial whose degree is exhausted by distinct roots in D divides its concrete locator. -/
theorem dvd_subspacePolynomial_of_root_count {B : Type*} [Field B]
    (D : AddSubgroup B) [Fintype D] (P : B[X]) (hP : P ≠ 0)
    (hcard : Nat.card {x : D // P.eval (x : B)=0} = P.natDegree) :
    P ∣ subspacePolynomial D ∧ P.Separable := by
  classical
  let S := Finset.univ.image (fun x : {x : D // P.eval (x : B)=0} ↦ (x.val : B))
  have hinj : Function.Injective (fun x : {x : D // P.eval (x : B)=0} ↦ (x.val : B)) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have hS : S.card=P.natDegree := by
    rw [Finset.card_image_iff.mpr hinj.injOn, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hroot : ∀ x ∈ S, P.eval x=0 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hroots := roots_eq_of_natDegree_le_card_of_ne_zero hroot hS.ge hP
  have hsplit : P.Splits := splits_iff_card_roots.mpr (by rw [hroots]; exact hS)
  refine ⟨hsplit.dvd_of_roots_le_roots hP ?_,
    (nodup_roots_iff_of_splits hP hsplit).mp (hroots ▸ S.nodup)⟩
  rw [hroots]
  apply Finset.val_le_iff_val_subset.mpr
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_roots (subspacePolynomial_monic D).ne_zero).mpr
  exact (subspacePolynomial_eval_eq_zero_iff D (y.val : B)).mpr y.val.property
/-- The majority root count from the Walsh calculation supplies the exact factorization needed by the quotient construction. -/
theorem repairedPolynomial_dvd_locator (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-t)) :
    repairedPolynomial D v A l κ ∣ subspacePolynomial D ∧
      (repairedPolynomial D v A l κ).Separable := by
  have hdegree := (repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr).1
  apply dvd_subspacePolynomial_of_root_count D _
  · intro h
    rw [h, natDegree_zero] at hdegree
    have : 0 < (2:ℕ)^k+2^(k-t) := by positivity
    omega
  · rw [hdegree, ← hzeros]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [repairedPolynomial_eval, map_eq_zero]

end BinaryFieldCounterexamples.Gold
