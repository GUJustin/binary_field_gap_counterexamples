/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Pole reduction

Evaluation at an exterior pole turns polynomial corrections with common high
coefficients into challenges for one reciprocal received pair.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- The strict-degree witness obtained by taking the divided difference of a
correction polynomial at the pole. -/
noncomputable def poleCorrection {F : Type*} [Field F]
    (C : F[X]) (β : F) : F[X] :=
  -((C - Polynomial.C (C.eval β)) / (X - Polynomial.C β))

/-- A correction of degree at most `K` gives a pole witness of degree strictly
below `K`. -/
theorem poleCorrection_degree_lt
    {F : Type*} [Field F] (C : F[X]) (β : F) (K : ℕ)
    (hC : C.degree ≤ K) : (poleCorrection C β).degree < K := by
  let Q := C - Polynomial.C (C.eval β)
  by_cases hQ : Q = 0
  · simp [poleCorrection, Q, hQ]
  have hdiv : (Q / (X - Polynomial.C β)).degree < Q.degree :=
    degree_div_lt hQ (by simp)
  have hQdeg : Q.degree ≤ K := by
    exact (degree_sub_le _ _).trans (max_le hC
      (degree_C_le.trans (by exact_mod_cast Nat.zero_le K)))
  simpa only [poleCorrection, Q, degree_neg] using hdiv.trans_le hQdeg

/-- Away from the pole, the divided correction evaluates to the negative
divided difference. -/
theorem poleCorrection_eval
    {F : Type*} [Field F] (C : F[X]) (β x : F) (hx : x ≠ β) :
    (poleCorrection C β).eval x = -((C.eval x - C.eval β) / (x - β)) := by
  let Q := C - Polynomial.C (C.eval β)
  have hroot : Q.IsRoot β := by simp [Q, IsRoot]
  have hmul : (X - Polynomial.C β) * (Q / (X - Polynomial.C β)) = Q :=
    (mul_div_eq_iff_isRoot (p := Q) (a := β)).2 hroot
  have heval := congrArg (Polynomial.eval x) hmul
  have hx' : x - β ≠ 0 := sub_ne_zero.mpr hx
  simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
  have hquot : (Q / (X - Polynomial.C β)).eval x =
      (C.eval x - C.eval β) / (x - β) := by
    apply (eq_div_iff hx').2
    rw [mul_comm]
    simpa only [Q, eval_sub, eval_C] using heval
  rw [poleCorrection, eval_neg, hquot]

/-- Roots of `R+C` yield agreements for the pole-reduced word at challenge
`C(β)`. -/
theorem poleReduction_agreementGE
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (R C : F[X])
    (K T : ℕ) (hC : C.degree ≤ K)
    (hroots : T ≤ (D.filter fun x ↦ (R + C).eval x = 0).card) :
    agreementGE D K
      (fun x ↦ R.eval (x : F) * ((x : F) - β)⁻¹ +
        C.eval β * ((x : F) - β)⁻¹) T := by
  classical
  refine ⟨poleCorrection C β, poleCorrection_degree_lt C β K hC, ?_⟩
  rw [agreementCount_eq_card_filter D
      (fun x ↦ R.eval x * (x - β)⁻¹ + C.eval β * (x - β)⁻¹)
    (poleCorrection C β)]
  refine hroots.trans (Finset.card_le_card ?_)
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxD, hxroot⟩
  apply Finset.mem_filter.mpr
  refine ⟨hxD, ?_⟩
  have hxβ : x ≠ β := fun h ↦ hβ (h ▸ hxD)
  rw [poleCorrection_eval C β x hxβ]
  simp only [eval_add] at hxroot
  have hden : x - β ≠ 0 := sub_ne_zero.mpr hxβ
  field_simp
  linear_combination -hxroot

/-- Every correction satisfying the root and degree contracts contributes its
pole value to the exceptional set of the fixed reciprocal pair. -/
theorem poleReduction_badChallenge
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (R C : F[X])
    (K T : ℕ) (hC : C.degree ≤ K)
    (hroots : T ≤ (D.filter fun x ↦ (R + C).eval x = 0).card) :
    C.eval β ∈ badChallenges D K
      (fun x ↦ R.eval (x : F) * ((x : F) - β)⁻¹)
      (fun x ↦ ((x : F) - β)⁻¹) T := by
  rw [mem_badChallenges]
  exact poleReduction_agreementGE D β hβ R C K T hC hroots

end BinaryFieldCounterexamples
