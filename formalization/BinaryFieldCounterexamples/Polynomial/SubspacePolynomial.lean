/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.Ring

/-!
# Product locators of finite additive subgroups

The locator of `W` is the product of `X - w` over its elements. This
representation keeps the actual roots and applies to the trivial subgroup
as well. In characteristic two an additive subgroup is a binary linear space;
no choice of a basis is needed to define its locator.

These elementary product facts provide the root and degree interface for the
prescribed-domain construction in `MainTheorems.QuadraticNearJohnson`.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

variable {F : Type*} [Field F]

/-- The monic product locator of a finite additive subgroup. -/
noncomputable def subspacePolynomial (W : AddSubgroup F) [Fintype W] : F[X] :=
  ∏ w : W, (X - C (w : F))

/-- Every product locator is monic, including the locator `X` of `{0}`. -/
theorem subspacePolynomial_monic (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).Monic := by
  classical
  exact monic_prod_X_sub_C (fun w : W ↦ (w : F)) Finset.univ

/-- The locator degree is the number of elements of the subgroup. -/
@[simp] theorem subspacePolynomial_natDegree (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).natDegree = Fintype.card W := by
  classical
  simp [subspacePolynomial]

/-- The degree statement in the strict-degree convention used for codewords. -/
@[simp] theorem subspacePolynomial_degree (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).degree = (Fintype.card W : WithBot ℕ) := by
  rw [degree_eq_natDegree (subspacePolynomial_monic W).ne_zero,
    subspacePolynomial_natDegree]

/-- The roots of the locator are exactly the elements of the subgroup. -/
@[simp] theorem subspacePolynomial_eval_eq_zero_iff
    (W : AddSubgroup F) [Fintype W] (x : F) :
    (subspacePolynomial W).eval x = 0 ↔ x ∈ W := by
  classical
  simp only [subspacePolynomial, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  exact ⟨fun ⟨w, hw⟩ ↦ hw.symm ▸ w.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- An additive subgroup contains zero, so its locator has zero constant term. -/
@[simp] theorem subspacePolynomial_coeff_zero (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  exact (subspacePolynomial_eval_eq_zero_iff W 0).mpr W.zero_mem

/-- Equal product locators determine equal additive subgroups. -/
theorem subspacePolynomial_injective
    (U W : AddSubgroup F) [Fintype U] [Fintype W]
    (h : subspacePolynomial U = subspacePolynomial W) : U = W := by
  ext x
  rw [← subspacePolynomial_eval_eq_zero_iff U x,
    ← subspacePolynomial_eval_eq_zero_iff W x, h]

/-- Translating an input by a subgroup element permutes the factors. -/
theorem subspacePolynomial_eval_add_mem
    (W : AddSubgroup F) [Fintype W] (x : F) (w : W) :
    (subspacePolynomial W).eval (x + w) = (subspacePolynomial W).eval x := by
  classical
  simp only [subspacePolynomial, eval_prod, eval_sub, eval_X, eval_C]
  apply Fintype.prod_equiv (Equiv.addRight (-w))
  intro u
  change x + (w : F) - (u : F) = x - ((u : F) + -(w : F))
  ring

/-- The product locator is additive as a polynomial identity. The proof uses
translation of its roots and cancellation of the monic leading terms, so it
does not rely on an ambient finite field or a chosen binary basis. -/
theorem subspacePolynomial_comp_X_add_C
    (W : AddSubgroup F) [Fintype W] (y : F) :
    (subspacePolynomial W).comp (X + C y) =
      subspacePolynomial W + C ((subspacePolynomial W).eval y) := by
  classical
  let L := subspacePolynomial W
  let Q := L.comp (X + C y) - L - C (L.eval y)
  have hm : L.Monic := subspacePolynomial_monic W
  have hm' : (L.comp (X + C y)).Monic := hm.comp_X_add_C y
  have hd : (L.comp (X + C y)).degree = L.degree := by
    rw [degree_comp (by simp), degree_X_add_C, mul_one]
  have hcancel : (L.comp (X + C y) - L).degree < L.degree :=
    degree_sub_lt_right hd hm.ne_zero (by rw [hm'.leadingCoeff, hm.leadingCoeff])
  have hpos : (0 : WithBot ℕ) < L.degree := by
    rw [show L = subspacePolynomial W from rfl, subspacePolynomial_degree]
    exact_mod_cast Fintype.card_pos
  have hQdegree : Q.degree < (Fintype.card W : WithBot ℕ) := by
    rw [← subspacePolynomial_degree W]
    exact (degree_sub_le _ _).trans_lt
      (max_lt hcancel ((degree_C_le).trans_lt hpos))
  have hQ : Q = 0 := by
    by_cases hzero : Q = 0
    · exact hzero
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun w : W ↦ (w : F)) Subtype.val_injective
    · intro w
      have he := subspacePolynomial_eval_add_mem W y w
      have hw := (subspacePolynomial_eval_eq_zero_iff W (w : F)).mpr w.property
      simpa [Q, L, eval_comp, add_comm, hw] using sub_eq_zero.mpr he
    · exact (natDegree_lt_iff_degree_lt hzero).mpr hQdegree
  simpa [Q, add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hQ)

/-- Evaluating the polynomial identity gives an additive function. -/
theorem subspacePolynomial_eval_add
    (W : AddSubgroup F) [Fintype W] (x y : F) :
    (subspacePolynomial W).eval (x + y) =
      (subspacePolynomial W).eval x + (subspacePolynomial W).eval y := by
  have h := congrArg (fun p : F[X] ↦ p.eval x)
    (subspacePolynomial_comp_X_add_C W y)
  simpa using h

end BinaryFieldCounterexamples
