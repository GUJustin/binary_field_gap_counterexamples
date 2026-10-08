/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePolar
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRootBound
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
/-!
# Scalar-valued quadratic forms from the literal trace family

Frobenius-fixed values are lifted through the injective scalar inclusion.
The actual Frobenius monomials give degree-two homogeneity, and the proven
polar trace identity supplies the bilinear companion. Thus the resulting
Mathlib quadratic form is the same function as the original polynomial;
no rank, type, or population conclusion is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- A scalar-field Frobenius-fixed element lies in the actual scalar image. -/
theorem exists_scalar_of_frobenius_fixed (z : B) (hz : z^(Fintype.card k)=z) :
    ∃ c : k, algebraMap k B c=z := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
  intro f
  obtain ⟨r, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k B).surjective f
  have hf : (FiniteField.frobeniusAlgEquivOfAlgebraic k B) z=z := hz
  have hall (j : ℕ) : (FiniteField.frobeniusAlgEquivOfAlgebraic k B ^ j) z=z := by
    induction j with
    | zero => rfl
    | succ j hj => rw [pow_succ,AlgEquiv.mul_apply,hf,hj]
  exact hall r.val

/-- Every Frobenius monomial pair scales quadratically under scalar multiplication. -/
theorem frobenius_pair_smul (i j : ℕ) (c : k) (x : B) :
    (c • x)^((Fintype.card k)^i+(Fintype.card k)^j) =
      (c*c) • x^((Fintype.card k)^i+(Fintype.card k)^j) := by
  have hi := (FiniteFieldLocator.qPowerLinearMap (k:=k) (K:=B) i).map_smul c x
  have hj := (FiniteFieldLocator.qPowerLinearMap (k:=k) (K:=B) j).map_smul c x
  simp only [FiniteFieldLocator.qPowerLinearMap_apply] at hi hj
  rw [pow_add,hi,hj,pow_add]
  simp only [Algebra.smul_def,map_mul]
  ring

/-- The cyclic trace polynomial is homogeneous of degree two as a function. -/
theorem cyclicTracePolynomial_eval_smul (m i : ℕ) (a x : B) (c : k) :
    (cyclicTracePolynomial (k:=k) m i a).eval (c • x)=
      (c*c) • (cyclicTracePolynomial (k:=k) m i a).eval x := by
  simp only [cyclicTracePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    frobenius_pair_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Algebra.smul_def]
  ring

/-- The half-trace polynomial is homogeneous of degree two as a function. -/
theorem halfTracePolynomial_eval_smul (n : ℕ) (a x : B) (c : k) :
    (halfTracePolynomial (k:=k) n a).eval (c • x)=
      (c*c) • (halfTracePolynomial (k:=k) n a).eval x := by
  simp only [halfTracePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    frobenius_pair_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Algebra.smul_def]
  ring

/-- The literal trace family is homogeneous of degree two over the scalar field. -/
theorem traceFamilyPolynomial_eval_smul (n t : ℕ) (a : TraceFamilyIndex n t → B)
    (c x : B) (u : k) :
    (traceFamilyPolynomial (k:=k) n t a c).eval (u • x)=
      (u*u) • (traceFamilyPolynomial (k:=k) n t a c).eval x := by
  simp only [traceFamilyPolynomial,eval_add,eval_finsetSum,cyclicTracePolynomial_eval_smul,
    halfTracePolynomial_eval_smul,Finset.smul_sum,smul_add]
/-- The unique scalar-field lift of the concrete trace polynomial value. -/
noncomputable def traceFamilyValue (n t : ℕ) (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (x : B) : k :=
  Classical.choose (exists_scalar_of_frobenius_fixed
    ((traceFamilyPolynomial (k:=k) n t a c).eval x)
    (traceFamilyPolynomial_eval_fixed n t a c x hcard hc))

/-- The chosen scalar lift maps to the literal polynomial evaluation. -/
theorem algebraMap_traceFamilyValue (n t : ℕ) (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (x : B) :
    algebraMap k B (traceFamilyValue n t a c hcard hc x)=
      (traceFamilyPolynomial (k:=k) n t a c).eval x := by
  exact Classical.choose_spec (exists_scalar_of_frobenius_fixed _
    (traceFamilyPolynomial_eval_fixed n t a c x hcard hc))

/-- The actual scalar lift is quadratic under scalar multiplication. -/
theorem traceFamilyValue_smul (n t : ℕ) (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (u : k) (x : B) :
    traceFamilyValue n t a c hcard hc (u • x)=
      (u*u) • traceFamilyValue n t a c hcard hc x := by
  apply (algebraMap k B).injective
  simp only [smul_eq_mul,map_mul,algebraMap_traceFamilyValue]
  simpa only [Algebra.smul_def,map_mul] using
    traceFamilyPolynomial_eval_smul n t a c x u
/-- A scalar function with the actual trace-linear polar identity is a quadratic form. -/
noncomputable def quadraticFormOfTracePairing (f : B → k) (J : B →ₗ[k] B)
    (hsmul : ∀ (u : k) (x : B), f (u • x)=(u*u) • f x)
    (hpolar : ∀ x y : B, f (x+y)-f x-f y=Algebra.trace k B (y*J x)) :
    QuadraticForm k B :=
  QuadraticMap.ofPolar f hsmul
    (by
      intro x x' y
      simp only [QuadraticMap.polar,hpolar,map_add,mul_add])
    (by
      intro u x y
      simp only [QuadraticMap.polar,hpolar,map_smul,mul_smul_comm])
/-- The scalar lift has the actual trace derivative as its polar pairing. -/
theorem traceFamilyValue_polar (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (x y : B) :
    traceFamilyValue n t a c hcard hc (x+y)-traceFamilyValue n t a c hcard hc x-
      traceFamilyValue n t a c hcard hc y =
      Algebra.trace k B (y*traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c x) := by
  apply (algebraMap k B).injective
  simp only [map_sub,algebraMap_traceFamilyValue,traceFamilyDerivativeLinearMap_apply]
  exact traceFamilyPolynomial_polar n t ht htn hcard a c hc x y

/-- The concrete, scalar-valued quadratic form represented by the trace polynomial. -/
noncomputable def traceFamilyQuadraticForm (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) : QuadraticForm k B :=
  quadraticFormOfTracePairing (traceFamilyValue n t a c hcard hc)
    (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c)
    (traceFamilyValue_smul n t a c hcard hc)
    (traceFamilyValue_polar n t ht htn a c hcard hc)

/-- The packaged quadratic form evaluates to the original polynomial after scalar inclusion. -/
theorem algebraMap_traceFamilyQuadraticForm (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (x : B) :
    algebraMap k B (traceFamilyQuadraticForm n t ht htn a c hcard hc x)=
      (traceFamilyPolynomial (k:=k) n t a c).eval x := by
  exact algebraMap_traceFamilyValue n t a c hcard hc x

/-- The packaged form's canonical polar bilinear map is the actual derivative trace pairing. -/
theorem traceFamilyQuadraticForm_polarBilin (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (x y : B) :
    (traceFamilyQuadraticForm n t ht htn a c hcard hc).polarBilin x y=
      Algebra.trace k B (y*traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c x) := by
  exact traceFamilyValue_polar n t ht htn a c hcard hc x y
end BinaryFieldCounterexamples.QuadraticFormTrace
