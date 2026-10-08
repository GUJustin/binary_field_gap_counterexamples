/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadical
public import BinaryFieldCounterexamples.Polynomial.QuadraticDifferential
/-!
# Actual translated trace polynomials and their derivative cosets

Translation preserves the literal degree bound and scalar-field values,
giving the full-field locator differential identity. The derivative is the
original linearized derivative minus a constant, with unchanged Frobenius
exponent divisibility. Its zero set is exactly the translated polar kernel.
Vanishing on this entire coset requires the stated quadratic-radical equality;
it is not inferred merely from polar degeneracy in characteristic two.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The literal translated trace polynomial. -/
noncomputable def translatedTracePolynomial (n t : ℕ) (a : TraceFamilyIndex n t → B)
    (c v : B) : B[X] := (traceFamilyPolynomial (k:=k) n t a c).comp (X-C v)

/-- Translation is polynomial composition, hence evaluates at the translated field element. -/
theorem translatedTracePolynomial_eval (n t : ℕ) (a : TraceFamilyIndex n t → B)
    (c v x : B) :
    (translatedTracePolynomial (k:=k) n t a c v).eval x =
      (traceFamilyPolynomial (k:=k) n t a c).eval (x-v) := by
  simp [translatedTracePolynomial]

/-- Translation preserves the established upper bound on the literal polynomial degree. -/
theorem translatedTracePolynomial_natDegree_le (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B) :
    (translatedTracePolynomial (k:=k) n t a c v).natDegree ≤
      (Fintype.card k)^(2*n-1)+(Fintype.card k)^(2*n-t-1) := by
  unfold translatedTracePolynomial
  rw [natDegree_comp,natDegree_X_sub_C,mul_one]
  exact traceFamilyPolynomial_natDegree_le n t ht htn a c

/-- The translated function still takes its values in the actual scalar field. -/
theorem translatedTracePolynomial_eval_fixed (n t : ℕ)
    (a : TraceFamilyIndex n t → B) (c v x : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) :
    ((translatedTracePolynomial (k:=k) n t a c v).eval x)^(Fintype.card k)=
      (translatedTracePolynomial (k:=k) n t a c v).eval x := by
  rw [translatedTracePolynomial_eval]
  exact traceFamilyPolynomial_eval_fixed n t a c (x-v) hcard hc

/-- The derivative of the actual translated polynomial evaluates to the translated linear map. -/
theorem translatedTracePolynomial_derivative_eval (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v x : B) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x =
      traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c (x-v) := by
  simp [translatedTracePolynomial,derivative_comp,traceFamilyDerivativeLinearMap_apply]

/-- The actual derivative zero set is exactly the translated polar kernel. -/
theorem translatedTracePolynomial_derivative_zero_iff (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v x : B) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0 ↔
      x-v ∈ (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).ker := by
  rw [translatedTracePolynomial_derivative_eval,LinearMap.mem_ker]

/-- The translated polynomial vanishes on the translated quadratic radical. -/
theorem translatedTracePolynomial_zero_of_radical (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v x : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c)
    (hx : x-v ∈ (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical) :
    (translatedTracePolynomial (k:=k) n t a c v).eval x=0 := by
  rw [translatedTracePolynomial_eval,← algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc]
  rw [hx.1,map_zero]

/-- When the quadratic radical is the polar kernel, the translated derivative coset is a zero coset. -/
theorem translatedTracePolynomial_zero_of_derivative_zero (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v x : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c)
    (hrad : (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=
      (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin.ker)
    (hx : (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0) :
    (translatedTracePolynomial (k:=k) n t a c v).eval x=0 := by
  apply translatedTracePolynomial_zero_of_radical n t ht htn a c v x hcard hc
  rw [hrad,traceFamilyQuadraticForm_ker_polarBilin]
  exact (translatedTracePolynomial_derivative_zero_iff n t ht htn a c v x).mp hx
/-- The trace degree bound gives the strict degree comparison needed for differentiation. -/
theorem translatedTracePolynomial_degree_comparison (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Fintype.card k*(translatedTracePolynomial (k:=k) n t a c v).natDegree <
      2*Fintype.card B := by
  have h1 : Fintype.card k*(Fintype.card k)^(2*n-1)=(Fintype.card k)^(2*n) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : Fintype.card k*(Fintype.card k)^(2*n-t-1)=(Fintype.card k)^(2*n-t) := by
    rw [← pow_succ']; congr 1; omega
  have hlt : (Fintype.card k)^(2*n-t) < (Fintype.card k)^(2*n) := by
    apply (Nat.pow_lt_pow_iff_right Fintype.one_lt_card).mpr
    omega
  have hb := Nat.mul_le_mul_left (Fintype.card k)
    (translatedTracePolynomial_natDegree_le (k:=k) n t ht htn a c v)
  rw [Nat.mul_add,h1,h2] at hb
  rw [hcard]
  omega

/-- The actual translated full-field polynomial satisfies the exact locator differential identity. -/
theorem translatedTracePolynomial_differential (p r : ℕ) [Fact p.Prime] [CharP B p]
    (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) :
    let G := translatedTracePolynomial (k:=k) n t a c v
    let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
    G^(Fintype.card k)-G = -C ((L.coeff 1)⁻¹)*L*G.derivative := by
  dsimp only
  rw [hq]
  apply QuadraticLocatorConversion.differential_identity_on_scalar_submodule
    p r hr (⊤ : Submodule k B)
  · intro x hx
    rw [← hq]
    exact translatedTracePolynomial_eval_fixed n t a c v x hcard hc
  · have htop : Fintype.card (⊤ : Submodule k B)=Fintype.card B :=
      Fintype.card_congr (Submodule.topEquiv (R:=k) (M:=B)).toEquiv
    simpa only [← hq,htop] using
      translatedTracePolynomial_degree_comparison n t ht htn a c v hcard
/-- The derivative zero coset has exactly the cardinality of the actual polar kernel. -/
theorem translatedTracePolynomial_card_derivative_zero (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B) :
    Nat.card {x : B // (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0} =
      Nat.card (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).ker := by
  apply Nat.card_congr
  refine { toFun := fun x => ⟨x.val-v,
      (translatedTracePolynomial_derivative_zero_iff n t ht htn a c v x.val).mp x.property⟩
           invFun := fun x => ⟨x.val+v, ?_⟩
           left_inv := ?_
           right_inv := ?_ }
  · rw [translatedTracePolynomial_derivative_zero_iff n t ht htn]
    simpa only [add_sub_cancel_right] using x.property
  · intro x
    apply Subtype.ext
    simp
  · intro x
    apply Subtype.ext
    simp
/-- Translation does not turn a nonzero parameter's derivative into the zero polynomial. -/
theorem translatedTracePolynomial_derivative_ne_zero (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B) (hne : a≠0 ∨ c≠0) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative ≠ 0 := by
  intro he
  have h := congrArg (fun P : B[X] => P.comp (X+C v)) he
  simp only [translatedTracePolynomial,derivative_comp,derivative_sub,derivative_X,
    derivative_C,sub_zero,one_mul,comp_assoc,sub_comp,X_comp,C_comp,
    add_sub_cancel_right,comp_X,zero_comp] at h
  exact traceFamily_derivative_ne_zero n t ht htn a c hne h
/-- Translation changes the concrete derivative by exactly its constant evaluation. -/
theorem translatedTracePolynomial_derivative (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative =
      (traceFamilyPolynomial (k:=k) n t a c).derivative-
        C ((traceFamilyPolynomial (k:=k) n t a c).derivative.eval v) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun x : B => x)
    Function.injective_id
  · intro x
    rw [translatedTracePolynomial_derivative_eval n t ht htn,map_sub]
    simp only [traceFamilyDerivativeLinearMap_apply,eval_sub,eval_C]
  · have hdeg := traceFamily_derivative_natDegree_le (k:=k) n t ht htn a c
    have hlt : (Fintype.card k)^(2*n-t) < Fintype.card B := by
      rw [hcard]
      apply (Nat.pow_lt_pow_iff_right Fintype.one_lt_card).mpr
      omega
    apply max_lt
    · simp only [translatedTracePolynomial,derivative_comp,derivative_sub,derivative_X,
        derivative_C,sub_zero,one_mul,natDegree_comp,natDegree_X_sub_C,mul_one]
      exact hdeg.trans_lt hlt
    · apply (natDegree_sub_le _ _).trans_lt
      simp only [natDegree_C,max_zero]
      exact hdeg.trans_lt hlt

/-- Every exponent of the translated derivative is still divisible by the required Frobenius power. -/
theorem translatedTracePolynomial_derivative_support_dvd (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (e : ℕ) (he : e ∈ (translatedTracePolynomial (k:=k) n t a c v).derivative.support) :
    (Fintype.card k)^t ∣ e := by
  by_cases hz : e=0
  · simp [hz]
  apply traceFamily_derivative_support_dvd n t ht htn a c e
  rw [mem_support_iff] at he ⊢
  rw [translatedTracePolynomial_derivative n t ht htn a c v hcard,coeff_sub,
    coeff_C,ite_eq_right hz,sub_zero] at he
  exact he
end BinaryFieldCounterexamples.QuadraticFormTrace
