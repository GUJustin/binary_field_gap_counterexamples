/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.NormalForm

/-!
# Degree of Boolean functions in linear coordinates

The algebraic-normal-form degree in Section 6.2 (translation periods and essential
coordinates) is the total degree of the unique reduced polynomial, rather than
the degree of an arbitrary interpolant. This module supplies the arithmetic API
used in Lemmas 6.4 and 6.5. `DegreeAffine` proves independence of coordinates.

Degree is natural-valued: both the zero function and all other constants have
degree zero. Statements detecting the top monomial by parity consequently need
positive dimension.
-/

@[expose] public section
noncomputable section

namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- Total degree of the unique reduced polynomial representing a Boolean function. -/
def degree (f : (σ → ZMod 2) → ZMod 2) : ℕ := (anf f).totalDegree

/-- Every constant, including zero, has degree zero. -/
@[simp] theorem degree_const (c : ZMod 2) : degree (fun _ : σ → ZMod 2 => c) = 0 := by
  simp [degree, anf_const]

/-- Addition cannot create a monomial above both input degrees. -/
theorem degree_add_le (f g : (σ → ZMod 2) → ZMod 2) :
    degree (f + g) ≤ max (degree f) (degree g) := by
  simpa [degree, anf_add] using totalDegree_add (anf f) (anf g)

/-- Boolean multiplication includes reduction by `Xᵢ² = Xᵢ`, which cannot raise degree. -/
theorem degree_mul_le (f g : (σ → ZMod 2) → ZMod 2) :
    degree (f * g) ≤ degree f + degree g := by
  have h : anf (f * g) = reduction (anf f * anf g) := by
    unfold reduction
    congr 1
    funext x
    simp [anf_eval]
  rw [degree, h]
  exact (reduction_totalDegree_le _).trans (totalDegree_mul _ _)

/-- A reduced monomial uses each of the available coordinates at most once. -/
theorem degree_le_card (f : (σ → ZMod 2) → ZMod 2) : degree f ≤ Fintype.card σ := by
  classical
  unfold degree totalDegree
  apply Finset.sup_le
  intro d hd
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i, d i ≤ ∑ _i : σ, 1 := Finset.sum_le_sum fun i _ =>
      (monomial_le_degreeOf i hd).trans (anf_degreeOf_le_one f i)
    _ = Fintype.card σ := by simp

/-- Degree zero is equivalent to being a constant function. -/
theorem degree_eq_zero_iff (f : (σ → ZMod 2) → ZMod 2) :
    degree f = 0 ↔ ∃ c, f = fun _ => c := by
  constructor
  · intro h
    have hp := totalDegree_eq_zero_iff_eq_C.mp h
    refine ⟨(anf f).coeff 0, ?_⟩
    funext x
    simpa only [anf_eval, eval_C] using congrArg (eval x) hp
  · rintro ⟨c, rfl⟩
    exact degree_const c

/-- Complementing a nonconstant Boolean function preserves its degree. -/
theorem degree_complement (f : (σ → ZMod 2) → ZMod 2) (h : 1 ≤ degree f) :
    degree (f + fun _ => 1) = degree f := by
  unfold degree at *
  rw [anf_add, anf_const]
  apply totalDegree_add_eq_left_of_totalDegree_lt
  simpa only [totalDegree_C] using Nat.lt_of_lt_of_le Nat.zero_lt_one h

end BinaryFieldCounterexamples.BooleanFunctions
