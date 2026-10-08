/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.LocatorWitness
public import BinaryFieldCounterexamples.Constructions.Gold.QuotientLocator
/-!
# Distinctness of the concrete Gold locator family

A dual evaluation frame reads every alternating tensor coordinate from the
actual polar map. The square of the quotient locator recovers its discarded
factor; that polynomial recovers the tensor, linear repair, and binary level.
Thus the construction counts genuinely distinct polynomials, including
between different tensors, rather than merely different presentations.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- A dual evaluation frame recovers every alternating coordinate from the actual polar functional. -/
theorem tensorPolarFunctional_coordinate (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A : TensorCoordinates d) (i j : Fin d) (hij : i<j) :
    (tensorPolarFunctional D v A (x j)) (x i) = A ⟨(i,j),hij⟩ := by
  classical
  unfold tensorPolarFunctional
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single ⟨(i,j),hij⟩]
  · simp [hdual, hij.ne, hij.ne']
  · intro ab _ hab
    have hab' : ab.val.1<ab.val.2 := ab.property
    have hnot : ¬(ab.val.1=i ∧ ab.val.2=j) := by
      intro h
      apply hab
      apply Subtype.ext
      exact Prod.ext h.1 h.2
    have hreverse : ¬(ab.val.1=j ∧ ab.val.2=i) := by omega
    simp only [hdual]
    split_ifs <;> simp_all
  · simp
/-- Under a dual evaluation frame, different alternating tensors have different actual polar maps. -/
theorem tensorPolarMap_injective (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0) :
    Function.Injective (tensorPolarMap D v) := by
  intro A A' h
  funext ij
  have he := congrArg (fun f : D →ₗ[ZMod 2] (D →+ ZMod 2) ↦ f (x ij.val.2) (x ij.val.1)) h
  change (tensorPolarFunctional D v A (x ij.val.2)) (x ij.val.1) =
    (tensorPolarFunctional D v A' (x ij.val.2)) (x ij.val.1) at he
  rw [tensorPolarFunctional_coordinate D v x hdual A _ _ ij.property,
    tensorPolarFunctional_coordinate D v x hdual A' _ _ ij.property] at he
  exact he
/-- The square of a quotient locator determines the discarded factor uniquely. -/
theorem quotientLocator_injective_discarded {B : Type*} [Field B]
    (η₁ η₂ : B) (L U₁ H₁ U₂ H₂ : B[X]) (hL : L ≠ 0)
    (hH₁ : H₁ ≠ 0) (hH₂ : H₂ ≠ 0) (hdiv₁ : H₁ ∣ L) (hdiv₂ : H₂ ∣ L)
    (hAS₁ : H₁^2+H₁=C (η₁^2)*L*U₁^2) (hAS₂ : H₂^2+H₂=C (η₂^2)*L*U₂^2)
    (he : quotientLocator η₁ U₁ L H₁=quotientLocator η₂ U₂ L H₂) : H₁=H₂ := by
  have hsq := congrArg (fun P : B[X] ↦ P^2) he
  rw [quotientLocator_sq η₁ U₁ L H₁ hH₁ hdiv₁ hAS₁,
    quotientLocator_sq η₂ U₂ L H₂ hH₂ hdiv₂ hAS₂] at hsq
  have hQ := add_left_cancel hsq
  have hQne : L/H₁ ≠ 0 := by
    intro h
    have hm := EuclideanDomain.mul_div_cancel' hH₁ hdiv₁
    rw [h, mul_zero] at hm
    exact hL hm.symm
  apply mul_right_cancel₀ hQne
  rw [EuclideanDomain.mul_div_cancel' hH₁ hdiv₁, hQ, EuclideanDomain.mul_div_cancel' hH₂ hdiv₂]
/-- Equality of repaired polynomials recovers the binary constant. -/
theorem repairedPolynomial_eq_constant (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A A' : TensorCoordinates d)
    (l l' : D →+ ZMod 2) (κ κ' : ZMod 2)
    (h : repairedPolynomial D v A l κ=repairedPolynomial D v A' l' κ') : κ=κ' := by
  have he := congrArg (fun P : B[X] ↦ P.coeff 0) h
  simp only [repairedPolynomial, coeff_add, tensorPolynomial_coeff_zero,
    functionalPolynomial_coeff_zero, coeff_C_zero, zero_add] at he
  exact (algebraMap (ZMod 2) B).injective he
/-- Linear repairs do not obscure recovery of the tensor polar map. -/
theorem repairedPolynomial_eq_polarMap (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A A' : TensorCoordinates d)
    (l l' : D →+ ZMod 2) (κ κ' : ZMod 2)
    (h : repairedPolynomial D v A l κ=repairedPolynomial D v A' l' κ') :
    tensorPolarMap D v A=tensorPolarMap D v A' := by
  have hκ := repairedPolynomial_eq_constant D v A A' l l' κ κ' h
  subst κ'
  have hp (z : D) : tensorQuadraticFunction D v A z+l z=tensorQuadraticFunction D v A' z+l' z := by
    have he := congrArg (fun P : B[X] ↦ P.eval (z : B)) h
    rw [repairedPolynomial_eval, repairedPolynomial_eval] at he
    exact add_right_cancel ((algebraMap (ZMod 2) B).injective he)
  ext y x
  have he := hp (x+y)
  rw [tensorQuadraticFunction_add, tensorQuadraticFunction_add, map_add, map_add] at he
  linear_combination he - hp x - hp y
/-- Under a dual frame, an actual repaired polynomial recovers its tensor, repair, and level separately. -/
theorem repairedPolynomial_injective_parameters (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A A' : TensorCoordinates d) (l l' : D →+ ZMod 2) (κ κ' : ZMod 2)
    (h : repairedPolynomial D v A l κ=repairedPolynomial D v A' l' κ') :
    A=A' ∧ l=l' ∧ κ=κ' := by
  have hκ := repairedPolynomial_eq_constant D v A A' l l' κ κ' h
  have hA := tensorPolarMap_injective D v x hdual (repairedPolynomial_eq_polarMap D v A A' l l' κ κ' h)
  subst A'
  subst κ'
  have hl : functionalPolynomial D l=functionalPolynomial D l' := by
    exact add_left_cancel (add_right_cancel h)
  exact ⟨rfl, functionalPolynomial_injective D hl, rfl⟩

/-- Distinct tensor-repair-level triples give distinct actual quotient locators whenever the repaired factors divide the domain locator. -/
theorem repairedLocator_injective_parameters (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A A' : TensorCoordinates d) (l l' : D →+ ZMod 2) (κ κ' : ZMod 2)
    (t : ℕ) (ht : 1 ≤ t)
    (hM : ∀ r, 1 ≤ r → r<t → goldMoment D v A r=0)
    (hM' : ∀ r, 1 ≤ r → r<t → goldMoment D v A' r=0)
    (hH : repairedPolynomial D v A l κ ≠ 0) (hH' : repairedPolynomial D v A' l' κ' ≠ 0)
    (hdiv : repairedPolynomial D v A l κ ∣ subspacePolynomial D)
    (hdiv' : repairedPolynomial D v A' l' κ' ∣ subspacePolynomial D)
    (he : repairedLocator D v A l κ t=repairedLocator D v A' l' κ' t) :
    A=A' ∧ l=l' ∧ κ=κ' := by
  apply repairedPolynomial_injective_parameters D v x hdual A A' l l' κ κ'
  have hAS (A₀ : TensorCoordinates d) (l₀ : D →+ ZMod 2) (κ₀ : ZMod 2)
      (hM₀ : ∀ r, 1 ≤ r → r<t → goldMoment D v A₀ r=0) :
      repairedPolynomial D v A₀ l₀ κ₀ ^ 2+repairedPolynomial D v A₀ l₀ κ₀ =
        C (normalizingRoot D ^ 2)*subspacePolynomial D*
          repairedSquareRoot t (repairedPolynomial D v A₀ l₀ κ₀)^2 := by
    rw [repairedSquareRoot_sq t ht _ (repairedPolynomial_derivative_support D k hD v A₀ l₀ κ₀ t hM₀),
      repairedPolynomial_artinSchreier, normalizedLocator, normalizingRoot_sq]
  exact quotientLocator_injective_discarded _ _ _ _ _ _ _ (subspacePolynomial_monic D).ne_zero
    hH hH' hdiv hdiv' (hAS A l κ hM) (hAS A' l' κ' hM') he

end BinaryFieldCounterexamples.Gold
