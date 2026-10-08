/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Saturation
/-!
# The Gold quotient locator and its recovery identity

Starting with the actual factorization `H ∣ L` and the repaired
Artin--Schreier equation, the polynomial `η U (L/H)` keeps precisely the
complementary roots on the prescribed domain. Its square, derivative,
monicity, degree, and recovery identity follow algebraically. The recovery
denominator is nonzero off the domain, so collisions there force collisions
of derivatives.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [CharP B 2]
/-- The locator obtained by discarding the roots of the repaired quadratic polynomial. -/
noncomputable def quotientLocator (η : B) (U L H : B[X]) : B[X] := C η * U * (L / H)
/-- Cancelling the nonzero discarded factor gives the complementary Artin--Schreier factorization. -/
theorem quotientLocator_complement {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) :
    C (η^2) * (L/H) * U^2 = H+1 := by
  apply mul_left_cancel₀ hH
  calc
    H * (C (η^2) * (L/H) * U^2) = C (η^2) * (H*(L/H)) * U^2 := by ring
    _ = C (η^2)*L*U^2 := by rw [EuclideanDomain.mul_div_cancel' hH hdiv]
    _ = H*(H+1) := by rw [← hAS]; ring
/-- Multiplying the quotient locator by its derivative factor recovers the other binary level set. -/
theorem quotientLocator_mul_factor {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) :
    quotientLocator η U L H * (C η*U) = H+1 := by
  rw [← quotientLocator_complement η U L H hH hdiv hAS]
  simp only [quotientLocator, map_pow]
  ring
/-- The squared quotient locator differs from the original locator by the discarded quotient. -/
theorem quotientLocator_sq {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) :
    quotientLocator η U L H ^ 2 = L+L/H := by
  calc
    quotientLocator η U L H ^ 2 = (C (η^2)*(L/H)*U^2)*(L/H) := by
      simp only [quotientLocator, map_pow]; ring
    _ = (H+1)*(L/H) := by rw [quotientLocator_complement η U L H hH hdiv hAS]
    _ = L+L/H := by rw [add_mul, one_mul, EuclideanDomain.mul_div_cancel' hH hdiv]
/-- Formal differentiation recovers the exact scaled square-root derivative. -/
theorem quotientLocator_derivative {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hη : η ≠ 0) (hU : U ≠ 0) (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) (hH' : H.derivative=U^2) (hU' : U.derivative=0) :
    (quotientLocator η U L H).derivative = C (η⁻¹)*U := by
  have he := congrArg derivative (quotientLocator_mul_factor η U L H hH hdiv hAS)
  simp only [derivative_mul, derivative_C, zero_mul, hU', mul_zero, add_zero,
    derivative_add, derivative_one, hH'] at he
  apply mul_right_cancel₀ (mul_ne_zero (C_ne_zero.mpr hη) hU)
  rw [he]
  rw [show C (η⁻¹)*U*(C η*U) = (C (η⁻¹)*C η)*U^2 by ring,
    ← C_mul, inv_mul_cancel₀ hη, C_1, one_mul]
/-- The quotient locator satisfies the exact recovery identity used for distinctness and pole collisions. -/
theorem quotientLocator_recovery (η : B) (U L H : B[X])
    (hη : η ≠ 0) (hU : U ≠ 0) (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) (hH' : H.derivative=U^2) (hU' : U.derivative=0) :
    (quotientLocator η U L H).derivative * (quotientLocator η U L H ^ 2 + L) =
      C ((η^2)⁻¹) * quotientLocator η U L H := by
  rw [quotientLocator_derivative η U L H hη hU hH hdiv hAS hH' hU',
    quotientLocator_sq η U L H hH hdiv hAS]
  rw [show L+L/H+L=L/H by rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]]
  simp only [quotientLocator]
  rw [← inv_pow, map_pow]
  have hC : C (η⁻¹) * C η = (1 : B[X]) := by rw [← C_mul, inv_mul_cancel₀ hη, C_1]
  calc
    C (η⁻¹)*U*(L/H) = C (η⁻¹)*(C (η⁻¹)*C η)*U*(L/H) := by rw [hC, mul_one]
    _ = _ := by ring
/-- On the original locator's roots, the quotient construction keeps exactly the complementary level set. -/
theorem quotientLocator_eval_eq_zero_iff {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) (x : B) (hx : L.eval x=0) :
    (quotientLocator η U L H).eval x=0 ↔ H.eval x ≠ 0 := by
  constructor
  · intro hp hh
    have he := congrArg (fun P : B[X] ↦ P.eval x)
      (quotientLocator_mul_factor η U L H hH hdiv hAS)
    simp only [eval_mul, eval_add, eval_one, hp, hh, zero_mul, zero_add] at he
    exact zero_ne_one he
  · intro hh
    have he := congrArg (fun P : B[X] ↦ P.eval x) (EuclideanDomain.mul_div_cancel' hH hdiv)
    rw [eval_mul, hx] at he
    have hq := (mul_eq_zero.mp he).resolve_left hh
    simp only [quotientLocator, eval_mul, hq, mul_zero]
/-- A lower-degree discarded quotient leaves a monic quotient locator. -/
theorem quotientLocator_monic (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) (hL : L.Monic) (hd : (L/H).degree < L.degree) :
    (quotientLocator η U L H).Monic := by
  have hm : (quotientLocator η U L H ^ 2).Monic := by
    rw [quotientLocator_sq η U L H hH hdiv hAS]
    exact hL.add_of_left hd
  have he := hm.leadingCoeff
  rw [leadingCoeff_pow] at he
  change (quotientLocator η U L H).leadingCoeff = 1
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (show (quotientLocator η U L H).leadingCoeff^2 = (1:B)^2 by simpa using he) with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h
/-- The quotient locator has exactly half the original locator's degree. -/
theorem quotientLocator_natDegree {B : Type*} [Field B] (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L)
    (hAS : H^2+H=C (η^2)*L*U^2) (hd : (L/H).degree < L.degree) :
    (quotientLocator η U L H).natDegree = L.natDegree / 2 := by
  have he := congrArg natDegree (quotientLocator_sq η U L H hH hdiv hAS)
  rw [natDegree_pow, natDegree_add_eq_left_of_degree_lt hd] at he
  omega

/-- The quotient locator has exactly the complementary number of roots on a prescribed finite set. -/
theorem quotientLocator_root_count {B : Type*} [Field B] [DecidableEq B]
    (η : B) (U L H : B[X]) (S : Finset B)
    (hH : H ≠ 0) (hdiv : H ∣ L) (hAS : H^2+H=C (η^2)*L*U^2)
    (hS : ∀ x ∈ S, L.eval x=0) :
    (S.filter fun x ↦ (quotientLocator η U L H).eval x=0).card =
      S.card - (S.filter fun x ↦ H.eval x=0).card := by
  have he : S.filter (fun x ↦ (quotientLocator η U L H).eval x=0) =
      S.filter (fun x ↦ ¬ H.eval x=0) := by
    apply Finset.filter_congr
    intro x hx
    exact quotientLocator_eval_eq_zero_iff η U L H hH hdiv hAS x (hS x hx)
  rw [he]
  have hc := Finset.card_filter_add_card_filter_not (s := S) (fun x : B ↦ H.eval x=0)
  omega
/-- Away from the original domain, the denominator in the recovery identity cannot vanish. -/
theorem quotientLocator_recovery_denominator_ne_zero (η : B) (U L H : B[X])
    (hH : H ≠ 0) (hdiv : H ∣ L) (hAS : H^2+H=C (η^2)*L*U^2)
    (x : B) (hx : L.eval x ≠ 0) :
    (quotientLocator η U L H).eval x ^ 2 + L.eval x ≠ 0 := by
  have he := congrArg (fun P : B[X] ↦ P.eval x) (quotientLocator_sq η U L H hH hdiv hAS)
  rw [eval_pow, eval_add] at he
  rw [he, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  intro hq
  have hm := congrArg (fun P : B[X] ↦ P.eval x) (EuclideanDomain.mul_div_cancel' hH hdiv)
  rw [eval_mul, hq, mul_zero] at hm
  exact hx hm.symm
/-- A collision outside the prescribed domain forces a collision of the formal derivatives. -/
theorem quotientLocator_collision_derivative (η : B) (L U₁ H₁ U₂ H₂ : B[X])
    (hη : η ≠ 0) (hU₁ : U₁ ≠ 0) (hU₂ : U₂ ≠ 0)
    (hH₁ : H₁ ≠ 0) (hH₂ : H₂ ≠ 0) (hdiv₁ : H₁ ∣ L) (hdiv₂ : H₂ ∣ L)
    (hAS₁ : H₁^2+H₁=C (η^2)*L*U₁^2) (hAS₂ : H₂^2+H₂=C (η^2)*L*U₂^2)
    (hH₁' : H₁.derivative=U₁^2) (hH₂' : H₂.derivative=U₂^2)
    (hU₁' : U₁.derivative=0) (hU₂' : U₂.derivative=0)
    (x : B) (hx : L.eval x ≠ 0)
    (he : (quotientLocator η U₁ L H₁).eval x=(quotientLocator η U₂ L H₂).eval x) :
    (quotientLocator η U₁ L H₁).derivative.eval x =
      (quotientLocator η U₂ L H₂).derivative.eval x := by
  have h₁ := congrArg (fun P : B[X] ↦ P.eval x)
    (quotientLocator_recovery η U₁ L H₁ hη hU₁ hH₁ hdiv₁ hAS₁ hH₁' hU₁')
  have h₂ := congrArg (fun P : B[X] ↦ P.eval x)
    (quotientLocator_recovery η U₂ L H₂ hη hU₂ hH₂ hdiv₂ hAS₂ hH₂' hU₂')
  simp only [eval_mul, eval_add, eval_pow, eval_C] at h₁ h₂
  rw [he] at h₁
  exact mul_right_cancel₀ (quotientLocator_recovery_denominator_ne_zero η U₂ L H₂ hH₂ hdiv₂ hAS₂ x hx)
    (h₁.trans h₂.symm)

end BinaryFieldCounterexamples.Gold
