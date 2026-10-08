/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Labels
/-!
# Exact agreement points of a classified quadratic explaining polynomial

The literal polynomial identity forces agreement at a base-field point exactly
when it is a nonzero root of the same subgroup locator. The exterior coefficient
excludes the second quadratic factor. At zero the derivative identity and the
nonzero locator derivative make the explaining polynomial nonzero.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
/-- The literal explaining-polynomial identity has precisely the nonzero roots
of the actual base-field locator as agreement points. -/
theorem quadratic_classification_exact_agreement
    {B F : Type*} [Field B] [CharP B 2] [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ)
    (W : AddSubgroup B) [Fintype W] (K : ℕ) (hK : 2≤K)
    (a : B) (z : F) (p : F[X])
    (hid : X*p=(subspacePolynomial W).map φ^2+
      C (φ (a^2)+θ)*(subspacePolynomial W).map φ+
      X^(8*K)+C θ*X^(4*K)+C z*X^(2*K)) :
    ∀ x : B, p.eval (φ x)=(φ x)^(8*K-1)+θ*(φ x)^(4*K-1)+z*(φ x)^(2*K-1)
      ↔ x∈W ∧ x≠0 := by
  have hc : φ (a^2)+θ≠0 := by
    intro hh
    have h := CharTwo.add_eq_zero.mp hh
    exact hθ ⟨a^2,h⟩
  have hlin : φ ((subspacePolynomial W).coeff 1)≠0 :=
    fun h=>subspacePolynomial_coeff_one_ne_zero W (φ.injective (by simpa using h))
  have hp0 : p.eval 0=(φ (a^2)+θ)*φ ((subspacePolynomial W).coeff 1) := by
    have he := congrArg (fun R:F[X]=>R.derivative.eval 0) hid
    simpa [derivative_mul,derivative_pow,derivative_add,derivative_map,
      eval_map,eval_mul,eval_add,eval_C,eval_X,eval_pow,
      Nat.cast_mul,CharTwo.two_eq_zero,show 8*K-1≠0 by omega,
      show 4*K-1≠0 by omega,show 2*K-1≠0 by omega,coeff_derivative,
      ←coeff_zero_eq_eval_zero] using he
  intro x
  by_cases hx : x=0
  · subst x
    have hpne : p.eval 0≠0 := by rw [hp0];exact mul_ne_zero hc hlin
    simp [show 8*K-1≠0 by omega,show 4*K-1≠0 by omega,show 2*K-1≠0 by omega,hpne]
  have hxF : φ x≠0 := fun hh=>hx (φ.injective (by simpa using hh))
  have he := congrArg (fun R:F[X]=>R.eval (φ x)) hid
  simp only [eval_mul,eval_X,eval_add,eval_pow,eval_C] at he
  have hmap : ((subspacePolynomial W).map φ).eval (φ x)=φ ((subspacePolynomial W).eval x) := by
    simp
  rw [hmap] at he
  have hnot : φ ((subspacePolynomial W).eval x)+(φ (a^2)+θ)≠0 := by
    intro hh
    have hz : φ ((subspacePolynomial W).eval x+a^2)=θ := by
      apply CharTwo.add_eq_zero.mp
      simpa only [map_add,add_assoc] using hh
    exact hθ ⟨_,hz⟩
  have hpowers (r:ℕ) (hr:0<r) : φ x*(φ x)^(r-1)=(φ x)^r := by
    rw [←pow_succ',Nat.sub_add_cancel hr]
  have he' : φ x*(p.eval (φ x)+((φ x)^(8*K-1)+θ*(φ x)^(4*K-1)+z*(φ x)^(2*K-1)))=
      φ ((subspacePolynomial W).eval x)*(φ ((subspacePolynomial W).eval x)+(φ (a^2)+θ)) := by
    rw [mul_add,he]
    simp only [mul_add]
    rw [hpowers (8*K) (by omega)]
    have h4 : φ x*(θ*(φ x)^(4*K-1))=θ*(φ x)^(4*K) := by
      rw [mul_left_comm,hpowers (4*K) (by omega)]
    have h2 : φ x*(z*(φ x)^(2*K-1))=z*(φ x)^(2*K) := by
      rw [mul_left_comm,hpowers (2*K) (by omega)]
    rw [h4,h2]
    ring_nf
    simp [CharTwo.two_eq_zero]
  rw [←CharTwo.add_eq_zero]
  rw [←mul_eq_zero_iff_left hxF,he',mul_eq_zero_iff_right hnot]
  rw [map_eq_zero_iff φ φ.injective,subspacePolynomial_eval_eq_zero_iff]
  simp [hx]
end BinaryFieldCounterexamples
