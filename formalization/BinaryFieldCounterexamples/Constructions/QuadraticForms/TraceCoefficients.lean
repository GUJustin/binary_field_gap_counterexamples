/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePolynomial

/-!
# Literal coefficient recovery in the quadratic trace family

The derivative coefficients below and at the middle index recover every actual
family parameter, including in characteristic two. A nonzero parameter has a
nonzero derivative, whose degree and exponent divisibility give the concrete
input needed for Frobenius root counting.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Distinct scalar-field Frobenius exponents recover literal monomial coefficients. -/
theorem coeff_frobenius_monomial (a : B) (i j : ℕ) :
    (C a*X^((Fintype.card k)^i)).coeff ((Fintype.card k)^j)=if i=j then a else 0 := by
  by_cases h : i=j
  · subst j
    simp
  · have hp : (Fintype.card k)^i≠(Fintype.card k)^j := by
      intro he
      exact h (Nat.pow_right_injective Fintype.one_lt_card he)
    simp [coeff_C_mul,coeff_X_pow,h,Ne.symm hp]
/-- Every off-middle trace parameter is its actual derivative coefficient. -/
theorem traceFamily_derivative_coeff_low (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) (i : TraceFamilyIndex n t) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative.coeff ((Fintype.card k)^i.val.val)=a i := by
  rw [traceFamilyPolynomial_derivative n t ht htn,coeff_add,finsetSum_coeff,
    coeff_frobenius_monomial]
  have hi : i.val.val < n := i.val.isLt
  rw [ite_eq_right (show n≠i.val.val by omega),add_zero,Finset.sum_eq_single i]
  · rw [coeff_add,coeff_frobenius_monomial,coeff_frobenius_monomial]
    simp [show 2*n-i.val.val≠i.val.val by omega]
  · intro j hj hji
    have hjn : j.val.val < n := j.val.isLt
    have hv : j.val.val≠i.val.val := by
      intro he
      apply hji
      apply Subtype.ext
      exact Fin.ext he
    rw [coeff_add,coeff_frobenius_monomial,coeff_frobenius_monomial]
    simp [hv,show 2*n-j.val.val≠i.val.val by omega]
  · simp
/-- The middle trace parameter is its actual derivative coefficient. -/
theorem traceFamily_derivative_coeff_middle (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative.coeff ((Fintype.card k)^n)=c := by
  rw [traceFamilyPolynomial_derivative n t ht htn,coeff_add,finsetSum_coeff,
    coeff_frobenius_monomial,ite_eq_left rfl]
  have hz : (∑ i : TraceFamilyIndex n t,
      (C (a i)*X^((Fintype.card k)^i.val.val)+
        C ((a i)^((Fintype.card k)^(2*n-i.val.val)))*X^((Fintype.card k)^(2*n-i.val.val))).coeff
        ((Fintype.card k)^n))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i.val.val < n := i.val.isLt
    rw [coeff_add,coeff_frobenius_monomial,coeff_frobenius_monomial]
    simp [show i.val.val≠n by omega,show 2*n-i.val.val≠n by omega]
  rw [hz,zero_add]
/-- The literal derivative recovers every trace-family parameter in every characteristic. -/
theorem traceFamily_parameters_eq_of_derivative_eq (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a a' : TraceFamilyIndex n t → B) (c c' : B)
    (he : (traceFamilyPolynomial (k:=k) n t a c).derivative=
      (traceFamilyPolynomial (k:=k) n t a' c').derivative) : a=a' ∧ c=c' := by
  constructor
  · funext i
    have h := congrArg (fun P : B[X] => P.coeff ((Fintype.card k)^i.val.val)) he
    simpa only [traceFamily_derivative_coeff_low n t ht htn] using h
  · have h := congrArg (fun P : B[X] => P.coeff ((Fintype.card k)^n)) he
    simpa only [traceFamily_derivative_coeff_middle n t ht htn] using h
/-- The actual trace-family parameterization remains injective after differentiation. -/
theorem traceFamily_derivative_injective (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) :
    Function.Injective (fun p : (TraceFamilyIndex n t → B) × B =>
      (traceFamilyPolynomial (k:=k) n t p.1 p.2).derivative) := by
  intro p q he
  obtain ⟨ha,hc⟩ := traceFamily_parameters_eq_of_derivative_eq n t ht htn p.1 q.1 p.2 q.2 he
  exact Prod.ext ha hc
/-- Zero parameters give the literal zero polynomial. -/
theorem traceFamilyPolynomial_zero (n t : ℕ) :
    traceFamilyPolynomial (k:=k) (B:=B) n t 0 0=0 := by
  simp [traceFamilyPolynomial,cyclicTracePolynomial,halfTracePolynomial]
/-- A nonzero trace parameter produces a genuinely nonzero derivative. -/
theorem traceFamily_derivative_ne_zero (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) (hne : a≠0 ∨ c≠0) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative≠0 := by
  intro hz
  have he : (traceFamilyPolynomial (k:=k) n t a c).derivative=
      (traceFamilyPolynomial (k:=k) n t 0 0).derivative := by
    rw [traceFamilyPolynomial_zero,derivative_zero,hz]
  obtain ⟨ha,hc⟩ := traceFamily_parameters_eq_of_derivative_eq n t ht htn a 0 c 0 he
  exact hne.elim (fun h => h ha) (fun h => h hc)
/-- The derivative's highest possible Frobenius index is literally `2n-t`. -/
theorem traceFamily_derivative_natDegree_le (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative.natDegree ≤ (Fintype.card k)^(2*n-t) := by
  rw [traceFamilyPolynomial_derivative n t ht htn]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hil := i.property
    have hiu := i.val.isLt
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_X_pow]
      exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_X_pow]
      exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_X_pow]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
/-- Every supported derivative exponent is divisible by the required
lowest Frobenius power, with no implicit polynomial-function reduction. -/
theorem traceFamily_derivative_support_dvd (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) (e : ℕ)
    (he : e∈(traceFamilyPolynomial (k:=k) n t a c).derivative.support) :
    (Fintype.card k)^t ∣ e := by
  by_contra hne
  have hmon (z : B) (j : ℕ) (hj : t ≤ j) :
      (C z*X^((Fintype.card k)^j)).coeff e=0 := by
    have hexp : (Fintype.card k)^j≠e := by
      intro heq
      apply hne
      rw [←heq]
      exact pow_dvd_pow _ hj
    simp [coeff_C_mul,coeff_X_pow,Ne.symm hexp]
  have hz : (traceFamilyPolynomial (k:=k) n t a c).derivative.coeff e=0 := by
    rw [traceFamilyPolynomial_derivative n t ht htn,coeff_add,finsetSum_coeff,hmon c n htn,add_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hil := i.property
    have hiu := i.val.isLt
    rw [coeff_add,hmon (a i) i.val.val hil,
      hmon ((a i)^((Fintype.card k)^(2*n-i.val.val))) (2*n-i.val.val) (by omega),add_zero]
  exact (mem_support_iff.mp he) hz
end BinaryFieldCounterexamples.QuadraticFormTrace
