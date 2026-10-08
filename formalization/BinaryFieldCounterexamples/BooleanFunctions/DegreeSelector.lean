/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.DegreeLeading
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Extracting the selector coefficient

In the proof of Lemma 6.5, the degree bound on `ℓ φ` forces the next-degree
part of `(u+v+c)(Ω₀+Ω₁)` to vanish. This module isolates that implication using
the coefficient of the selector variable in the reduced polynomial. The
children need not themselves be trees.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- A Boolean branch with its selector adjoined as a fresh coordinate. -/
def selectorBranchPolynomial (p₀ p₁ : MvPolynomial σ (ZMod 2)) :
    MvPolynomial (Option σ) (ZMod 2) :=
  rename Option.some p₀ + X none * rename Option.some (p₀ + p₁)

/-- Split a linear form into its selector coefficient and its remaining coordinates. -/
def selectorLinearPolynomial (a : ZMod 2) (r : MvPolynomial σ (ZMod 2)) :
    MvPolynomial (Option σ) (ZMod 2) := C a * X none + rename Option.some r

/-- Shannon expansion of the reduced product with a split linear form. -/
theorem reduction_selector_product (a : ZMod 2) (r p₀ p₁ : MvPolynomial σ (ZMod 2)) :
    reduction (selectorLinearPolynomial a r * selectorBranchPolynomial p₀ p₁) =
      rename Option.some (reduction (r * p₀)) +
        X none * rename Option.some (reduction (C a * p₁ + r * (p₀ + p₁))) := by
  apply anf_unique
  · apply (restrictDegree (Option σ) (ZMod 2) 1).add_mem
    · exact rename_mem_restrictDegree _ (Option.some_injective _) _ (anf_mem_restrictDegree _)
    · apply X_mul_mem_restrictDegree
      · exact rename_mem_restrictDegree _ (Option.some_injective _) _ (anf_mem_restrictDegree _)
      · exact degreeOf_rename_of_not_mem_range _ (Option.some_injective _) _ none (by simp)
  · intro x
    have hx : x none = 0 ∨ x none = 1 := (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) _
    rcases hx with hx | hx <;>
      simp [selectorLinearPolynomial, selectorBranchPolynomial, reduction_eval, eval_rename, hx]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide]

omit [Fintype σ] in
/-- Adjoining a selector makes a polynomial's coefficient of selector degree one
literally the second polynomial in its Shannon expansion. -/
theorem optionEquivLeft_coeff_selector (p q : MvPolynomial σ (ZMod 2)) :
    (optionEquivLeft (ZMod 2) σ (rename Option.some p + X none * rename Option.some q)).coeff 1 = q := by
  have hrename (r : MvPolynomial σ (ZMod 2)) :
      optionEquivLeft (ZMod 2) σ (rename Option.some r) = Polynomial.C r := by
    induction r using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  simp [hrename, Polynomial.coeff_mul_X]

omit [Fintype σ] in
/-- A bound on the whole polynomial bounds the selector coefficient one degree lower. -/
theorem totalDegree_selector_coefficient_le (P : MvPolynomial (Option σ) (ZMod 2))
    {k : ℕ} (hP : P.totalDegree ≤ k + 1) :
    ((optionEquivLeft (ZMod 2) σ P).coeff 1).totalDegree ≤ k := by
  by_cases hz : P.totalDegree = 0
  · have hp := totalDegree_eq_zero_iff_eq_C.mp hz
    rw [hp]
    simp
  · have hpos : 1 ≤ P.totalDegree := by omega
    have h := totalDegree_coeff_optionEquivLeft_add_le (ZMod 2) σ P 1 hpos
    omega

/-- The degree bound on `ℓ φ` kills the degree `k+1` part of the nonselector
linear form times the children's degree `k` part, precisely as in Lemma 6.5. -/
theorem homogeneousComponent_selector_product_eq_zero
    (a : ZMod 2) (r p₀ p₁ : MvPolynomial σ (ZMod 2)) {k : ℕ}
    (hk : 0 < k) (hr : r.totalDegree ≤ 1)
    (h₀ : p₀.totalDegree ≤ k) (h₁ : p₁.totalDegree ≤ k)
    (hprod : (reduction (selectorLinearPolynomial a r *
      selectorBranchPolynomial p₀ p₁)).totalDegree ≤ k + 1) :
    homogeneousComponent (k + 1)
      (reduction (r * homogeneousComponent k (p₀ + p₁))) = 0 := by
  have hcoeff := totalDegree_selector_coefficient_le _ hprod
  rw [reduction_selector_product, optionEquivLeft_coeff_selector] at hcoeff
  have hzero := homogeneousComponent_eq_zero (k + 1)
    (reduction (C a * p₁ + r * (p₀ + p₁))) (Nat.lt_succ_of_le hcoeff)
  have ha : (reduction (C a * p₁)).totalDegree < k + 1 := by
    have hb := (reduction_totalDegree_le (C a * p₁)).trans (totalDegree_mul _ _)
    simp only [totalDegree_C, zero_add] at hb
    omega
  rw [reduction_add, map_add, homogeneousComponent_eq_zero _ _ ha, zero_add] at hzero
  rw [homogeneousComponent_reduction_mul_top r (p₀ + p₁) hk hr
    ((totalDegree_add _ _).trans (max_le h₀ h₁))] at hzero
  exact hzero

end BinaryFieldCounterexamples.BooleanFunctions
