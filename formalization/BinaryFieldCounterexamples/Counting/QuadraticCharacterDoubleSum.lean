/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Double-sum expansion of finite character weights

A unit-norm additive character turns the squared norm of a finite Fourier sum
into its literal double correlation sum.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open scoped ComplexConjugate

/-- A unit-norm additive character sends negation to complex conjugation. -/
theorem addChar_conj_eq_neg {k : Type*} [AddCommGroup k]
    (χ : AddChar k ℂ) (hnorm : ∀ a, Complex.normSq (χ a) = 1) (a : k) :
    conj (χ a) = χ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, hnorm]
  simp

/-- The squared norm of a finite character sum is its literal double
correlation sum. -/
theorem normSq_character_sum_eq_double_sum
    {Q k : Type*} [AddCommGroup Q] [AddCommGroup k]
    (Y : Finset Q) (χ : AddChar k ℂ) (pair : Q → k)
    (hnorm : ∀ a, Complex.normSq (χ a) = 1)
    (hpair : ∀ x y, pair (x - y) = pair x - pair y) :
    (Complex.normSq (∑ x ∈ Y, χ (pair x)) : ℂ) =
      ∑ y ∈ Y, ∑ x ∈ Y, χ (pair (x - y)) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hpair, sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [← addChar_conj_eq_neg χ hnorm]
  ring

end BinaryFieldCounterexamples
