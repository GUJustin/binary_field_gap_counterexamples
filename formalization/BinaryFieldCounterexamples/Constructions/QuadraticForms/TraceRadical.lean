/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceQuadratic
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
/-!
# Actual polar kernels, quadratic radicals, and parameter recovery

The trace pairing identifies the polar kernel with the concrete derivative
kernel. The quadratic radical is only asserted to be contained in that
kernel, which is essential in characteristic two. The established derivative
root bound supplies both rank bounds. Finally, nondegeneracy and strict
polynomial degree recover every family parameter from the actual polar form.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The polar kernel is exactly the kernel of the literal derivative evaluation map. -/
theorem traceFamilyQuadraticForm_ker_polarBilin (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) :
    (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin.ker =
      (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).ker := by
  ext x
  simp only [LinearMap.mem_ker,LinearMap.ext_iff,LinearMap.zero_apply,
    traceFamilyQuadraticForm_polarBilin]
  constructor
  · intro h
    apply (trace_pairing_eq_zero_iff (k:=k) _).mp
    intro y
    rw [h y,map_zero]
  · intro h y
    rw [h,mul_zero,map_zero]

/-- The actual polar rank equals the rank of the concrete derivative map. -/
theorem traceFamilyQuadraticForm_polar_rank (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) :
    Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin.range =
      Module.finrank k (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).range := by
  have hQ := (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin.finrank_range_add_finrank_ker
  have hJ := (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).finrank_range_add_finrank_ker
  rw [traceFamilyQuadraticForm_ker_polarBilin] at hQ
  omega

/-- A nonzero actual family parameter has polar rank at least twice the start index. -/
theorem traceFamilyQuadraticForm_polar_rank_ge (p r : ℕ) [Fact p.Prime] [CharP B p]
    (hq : Fintype.card k=p^r) (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0) :
    2*t ≤ Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin.range := by
  rw [traceFamilyQuadraticForm_polar_rank]
  exact traceFamilyDerivativeLinearMap_rank_ge p r hq n t ht htn hcard a c hne

/-- The quadratic radical lies in the derivative kernel, also in characteristic two. -/
theorem traceFamilyQuadraticForm_radical_le (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) :
    (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical ≤
      (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).ker := by
  rw [← traceFamilyQuadraticForm_ker_polarBilin n t ht htn a c hcard hc]
  exact QuadraticMap.radical_le_ker_polarBilin

/-- The actual quadratic radical has codimension at least twice the start index. -/
theorem traceFamilyQuadraticForm_radical_codim_ge (p r : ℕ) [Fact p.Prime] [CharP B p]
    (hq : Fintype.card k=p^r) (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0) :
    2*t ≤ Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical := by
  have hd := Submodule.finrank_mono (traceFamilyQuadraticForm_radical_le n t ht htn a c hcard hc)
  have hr := traceFamilyDerivativeLinearMap_rank_ge p r hq n t ht htn hcard a c hne
  have he := (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).finrank_range_add_finrank_ker
  omega
/-- Equality of the actual polar forms recovers every literal trace parameter. -/
theorem traceFamily_parameters_eq_of_polarBilin_eq (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a a' : TraceFamilyIndex n t → B) (c c' : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hc' : c'^((Fintype.card k)^n)=c')
    (he : (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin=
      (traceFamilyQuadraticForm n t ht htn a' c' hcard hc').polarBilin) :
    a=a' ∧ c=c' := by
  apply traceFamily_parameters_eq_of_derivative_eq (k:=k) n t ht htn
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun x : B => x)
    Function.injective_id
  · intro x
    apply sub_eq_zero.mp
    apply (trace_pairing_eq_zero_iff (k:=k) _).mp
    intro y
    have h := congrArg (fun P : B →ₗ[k] B →ₗ[k] k => P x y) he
    simp only [traceFamilyQuadraticForm_polarBilin,
      traceFamilyDerivativeLinearMap_apply] at h
    simp only [mul_sub,map_sub,h,sub_self,map_zero]
  · rw [hcard]
    apply lt_of_le_of_lt (max_le
      (traceFamily_derivative_natDegree_le n t ht htn a c)
      (traceFamily_derivative_natDegree_le n t ht htn a' c'))
    apply (Nat.pow_lt_pow_iff_right Fintype.one_lt_card).mpr
    omega

/-- Equality of the packaged quadratic forms recovers all actual parameters. -/
theorem traceFamily_parameters_eq_of_quadraticForm_eq (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a a' : TraceFamilyIndex n t → B) (c c' : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hc' : c'^((Fintype.card k)^n)=c')
    (he : traceFamilyQuadraticForm n t ht htn a c hcard hc=
      traceFamilyQuadraticForm n t ht htn a' c' hcard hc') : a=a' ∧ c=c' := by
  exact traceFamily_parameters_eq_of_polarBilin_eq n t ht htn a a' c c' hcard hc hc'
    (congrArg QuadraticMap.polarBilin he)
end BinaryFieldCounterexamples.QuadraticFormTrace
