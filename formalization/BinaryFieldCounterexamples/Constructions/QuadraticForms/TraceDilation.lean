/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceCode
/-!
# Input dilation of the actual quadratic trace family

Multiplication of the input changes the literal trace coefficients by the
corresponding norm monomials and preserves the middle coefficient condition.
Nonzero dilation preserves actual code membership, quadratic rank and radical
incidence, supplying the symmetry needed for prescribed hyperplane descent.
-/
@[expose] public section
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Input dilation acts on each literal cyclic coefficient by its norm monomial. -/
theorem cyclicTracePolynomial_eval_dilate (m i : ℕ) (a z x : B)
    (hcard : Fintype.card B=(Fintype.card k)^m) :
    (cyclicTracePolynomial (k:=k) m i a).eval (z*x)=
      (cyclicTracePolynomial (k:=k) m i (a*z^((Fintype.card k)^i+1))).eval x := by
  rw [cyclicTracePolynomial_eval_sum m i a (z*x) hcard,
    cyclicTracePolynomial_eval_sum m i _ x hcard]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow,mul_assoc]

/-- Input dilation acts on the literal half-trace coefficient by the middle norm monomial. -/
theorem halfTracePolynomial_eval_dilate (n : ℕ) (c z x : B) :
    (halfTracePolynomial (k:=k) n c).eval (z*x)=
      (halfTracePolynomial (k:=k) n (c*z^((Fintype.card k)^n+1))).eval x := by
  rw [halfTracePolynomial_eval_sum,halfTracePolynomial_eval_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow,mul_assoc]

/-- The entire concrete trace family is closed under input dilation at evaluation level. -/
theorem traceFamilyPolynomial_eval_dilate (n t : ℕ) (a : TraceFamilyIndex n t → B)
    (c z x : B) (hcard : Fintype.card B=(Fintype.card k)^(2*n)) :
    (traceFamilyPolynomial (k:=k) n t a c).eval (z*x)=
      (traceFamilyPolynomial (k:=k) n t (fun i => a i*z^((Fintype.card k)^i.val.val+1))
        (c*z^((Fintype.card k)^n+1))).eval x := by
  simp only [traceFamilyPolynomial,eval_add,eval_finsetSum]
  rw [halfTracePolynomial_eval_dilate]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact cyclicTracePolynomial_eval_dilate (2*n) i.val.val (a i) z x hcard

/-- The transformed middle coefficient still belongs to the actual half-field fixed subspace. -/
theorem halfCoefficient_dilate_fixed (n : ℕ) (c z : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n)=c) :
    (c*z^((Fintype.card k)^n+1))^((Fintype.card k)^n)=c*z^((Fintype.card k)^n+1) := by
  have he : (Fintype.card k)^n*(Fintype.card k)^n=(Fintype.card k)^(2*n) := by
    rw [←pow_add]
    congr 1
    omega
  rw [mul_pow,hc,pow_add,pow_one,mul_pow,←pow_mul,he,←hcard,FiniteField.pow_card]
  ring

/-- The transformed literal parameters package exactly the dilated quadratic form. -/
theorem traceFamilyQuadraticForm_dilate (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c z : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n)=c) :
    traceFamilyQuadraticForm n t ht htn (fun i => a i*z^((Fintype.card k)^i.val.val+1))
      (c*z^((Fintype.card k)^n+1)) hcard (halfCoefficient_dilate_fixed n c z hcard hc)=
      (traceFamilyQuadraticForm n t ht htn a c hcard hc).comp (LinearMap.mulLeft k z) := by
  ext x
  apply (algebraMap k B).injective
  simp only [QuadraticMap.comp_apply,LinearMap.mulLeft_apply]
  rw [algebraMap_traceFamilyQuadraticForm,algebraMap_traceFamilyQuadraticForm]
  exact (traceFamilyPolynomial_eval_dilate n t a c z x hcard).symm

/-- Input dilation preserves the actual trace code. -/
theorem traceQuadraticCode_comp_mul_mem (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (z : B) (Q : QuadraticForm k B)
    (hQ : Q∈traceQuadraticCode n t ht htn hcard) :
    Q.comp (LinearMap.mulLeft k z)∈traceQuadraticCode n t ht htn hcard := by
  obtain ⟨u,rfl⟩ := hQ
  have hc := (mem_halfCoefficientSpace n u.2.val).mp u.2.property
  refine ⟨⟨(fun i => u.1 i*z^((Fintype.card k)^i.val.val+1)),
    ⟨u.2.val*z^((Fintype.card k)^n+1),
      (mem_halfCoefficientSpace n _).mpr (halfCoefficient_dilate_fixed n u.2.val z hcard hc)⟩⟩,?_⟩
  exact traceFamilyQuadraticForm_dilate n t ht htn u.1 u.2.val z hcard hc

/-- Nonzero input dilation preserves quadratic-radical dimension. -/
theorem radical_finrank_comp_mul (Q : QuadraticForm k B) (z : B) (hz : z≠0) :
    Module.finrank k (Q.comp (LinearMap.mulLeft k z)).radical=Module.finrank k Q.radical := by
  let e := Units.mulLeftLinearEquiv k B (Units.mk0 z hz)
  have he : Q.Equivalent (Q.comp e.toLinearMap) := ⟨Q.isometryEquivOfCompLinearEquiv e⟩
  exact he.rank_radical_eq.symm

/-- Nonzero input dilation permutes the actual trace code. -/
theorem traceQuadraticCode_comp_mul_mem_iff (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (z : B) (hz : z≠0) (Q : QuadraticForm k B) :
    Q.comp (LinearMap.mulLeft k z)∈traceQuadraticCode n t ht htn hcard ↔
      Q∈traceQuadraticCode n t ht htn hcard := by
  constructor
  · intro hQ
    have hh := traceQuadraticCode_comp_mul_mem n t ht htn hcard z⁻¹
      (Q.comp (LinearMap.mulLeft k z)) hQ
    have he : (Q.comp (LinearMap.mulLeft k z)).comp (LinearMap.mulLeft k z⁻¹)=Q := by
      ext x
      simp [QuadraticMap.comp_apply,hz]
    rw [he] at hh
    exact hh
  · exact traceQuadraticCode_comp_mul_mem n t ht htn hcard z Q

/-- Radical incidence under nonzero dilation is the literal multiplication of the vector. -/
theorem mem_radical_comp_mul (Q : QuadraticForm k B) (z x : B) (hz : z≠0) :
    x∈(Q.comp (LinearMap.mulLeft k z)).radical ↔ z*x∈Q.radical := by
  rw [QuadraticMap.mem_radical_iff',QuadraticMap.mem_radical_iff']
  simp only [QuadraticMap.comp_apply,LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨hx,hh⟩
    refine ⟨hx,?_⟩
    intro y
    have h := hh (z⁻¹*y)
    simpa [mul_add,←mul_assoc,hz] using h
  · rintro ⟨hx,hh⟩
    refine ⟨hx,?_⟩
    intro y
    simpa only [mul_add] using hh (z*y)
end BinaryFieldCounterexamples.QuadraticFormTrace
