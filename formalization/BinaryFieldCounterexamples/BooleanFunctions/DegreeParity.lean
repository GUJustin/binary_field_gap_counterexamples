/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.Degree
public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Parity and the top Boolean monomial

The height-two argument in the paper's Lemma 6.4 observes that an indicator with
an even support has no cubic term. More generally, the coefficient of the
monomial containing every coordinate is the sum of all values of a reduced
Boolean polynomial. For a nonempty coordinate type this characterizes degree
strictly below the dimension. The nonempty hypothesis is necessary because
`MvPolynomial.totalDegree` assigns degree zero to the zero polynomial.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial
open scoped Classical

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The squarefree exponent vector containing every coordinate. -/
def fullExponent : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

omit [DecidableEq σ] in
@[simp] theorem fullExponent_apply (i : σ) : fullExponent i = 1 := by
  simp [fullExponent]

/-- Summing a squarefree monomial over all Boolean points keeps only the full
monomial. This is the characteristic-two cancellation behind the parity test. -/
theorem sum_eval_monomial (d : σ →₀ ℕ) (c : ZMod 2) (hd : ∀ i, d i ≤ 1) :
    (∑ x : σ → ZMod 2, eval x (monomial d c)) =
      if d = fullExponent then c else 0 := by
  classical
  have hsum (i : σ) : (∑ b : ZMod 2, b ^ d i) = if d i = 1 then 1 else 0 := by
    have hi := hd i
    interval_cases h : d i <;> decide
  simp_rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i (b : ZMod 2) => b ^ d i)]
  simp_rw [hsum]
  by_cases h : d = fullExponent
  · subst d
    simp
  · have hi : ∃ i, d i ≠ 1 := by
      by_contra h'
      apply h
      ext i
      simpa using (not_exists.mp h' i)
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right h, Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [hi]

/-- The coefficient of the full squarefree monomial equals the sum of the
values, for every polynomial with coordinate degrees at most one. -/
theorem fullExponent_coeff_eq_sum_eval (p : MvPolynomial σ (ZMod 2))
    (hp : ∀ i, p.degreeOf i ≤ 1) :
    p.coeff fullExponent = ∑ x : σ → ZMod 2, eval x p := by
  classical
  conv_rhs => rw [p.as_sum]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  have hsum : (∑ d ∈ p.support, ∑ x : σ → ZMod 2, eval x (monomial d (p.coeff d))) =
      ∑ d ∈ p.support, if d = fullExponent then p.coeff d else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    exact sum_eval_monomial d _ (fun i => degreeOf_le_iff.mp (hp i) d hd)
  rw [hsum]
  by_cases h : fullExponent ∈ p.support
  · rw [Finset.sum_eq_single fullExponent] <;> simp_all
  · have hc : p.coeff fullExponent = 0 := by simpa [mem_support_iff] using h
    rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have : d ≠ fullExponent := by intro he; exact h (he ▸ hd)
    simp [this]

omit [DecidableEq σ] in
/-- A squarefree exponent has maximal possible degree precisely when it
contains every coordinate. -/
theorem squarefree_sum_lt_card_iff (d : σ →₀ ℕ) (hd : ∀ i, d i ≤ 1) :
    d.sum (fun _ e => e) < Fintype.card σ ↔ d ≠ fullExponent := by
  classical
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  constructor
  · intro h he
    subst d
    simp at h
  · intro h
    have hi : ∃ i, d i < 1 := by
      by_contra h'
      apply h
      ext i
      have := not_exists.mp h' i
      have := hd i
      simp only [fullExponent_apply]
      omega
    obtain ⟨i, hi⟩ := hi
    calc
      ∑ i, d i < ∑ _i : σ, 1 :=
        Finset.sum_lt_sum (fun i _ => hd i) ⟨i, Finset.mem_univ i, hi⟩
      _ = Fintype.card σ := by simp

omit [DecidableEq σ] in
/-- For positive dimension, the full monomial is the only squarefree monomial
whose degree is not strictly below the dimension. -/
theorem totalDegree_lt_card_iff_fullExponent_coeff_eq_zero [Nonempty σ]
    (p : MvPolynomial σ (ZMod 2)) (hp : ∀ i, p.degreeOf i ≤ 1) :
    p.totalDegree < Fintype.card σ ↔ p.coeff fullExponent = 0 := by
  classical
  rw [totalDegree, Finset.sup_lt_iff Fintype.card_pos]
  have hiff : (∀ d ∈ p.support, d.sum (fun _ e => e) < Fintype.card σ) ↔
      (∀ d ∈ p.support, d ≠ fullExponent) := by
    apply forall_congr'
    intro d
    apply forall_congr'
    intro hd
    exact squarefree_sum_lt_card_iff d (fun i => degreeOf_le_iff.mp (hp i) d hd)
  rw [hiff]
  constructor
  · intro h
    simpa [mem_support_iff] using (show fullExponent ∉ p.support from fun hd => h fullExponent hd rfl)
  · intro h d hd he
    subst d
    exact (mem_support_iff.mp hd) h

/-- The sum of Boolean values is the cardinality of their support modulo two. -/
theorem sum_values_eq_support_card {α : Type*} [Fintype α] (f : α → ZMod 2) :
    (∑ x, f x) = ((Finset.univ.filter (fun x => f x = 1)).card : ZMod 2) := by
  classical
  have hf (x : α) : f x = if f x = 1 then 1 else 0 := by
    have h : f x = 0 ∨ f x = 1 := by
      have hval := (f x).val_lt
      have hc := (f x).natCast_zmod_val
      interval_cases h : (f x).val <;> simp_all
    rcases h with h | h <;> simp [h]
  conv_lhs => arg 2; ext x; rw [hf x]
  simp

/-- A reduced Boolean polynomial has degree strictly below a positive
coordinate dimension exactly when its support has even cardinality. -/
theorem totalDegree_lt_card_iff_even_support [Nonempty σ]
    (p : MvPolynomial σ (ZMod 2)) (hp : ∀ i, p.degreeOf i ≤ 1) :
    p.totalDegree < Fintype.card σ ↔
      Even (Finset.univ.filter (fun x : σ → ZMod 2 => eval x p = 1)).card := by
  rw [totalDegree_lt_card_iff_fullExponent_coeff_eq_zero p hp,
    fullExponent_coeff_eq_sum_eval p hp, sum_values_eq_support_card,
    ZMod.natCast_eq_zero_iff_even]

/-- A Boolean function on a positive-dimensional coordinate space has degree
below the dimension exactly when it takes the value one at an even number of
points. This is the parity test used in the height-two proof of Lemma 6.4. -/
theorem degree_lt_card_iff_even_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (f : (ι → ZMod 2) → ZMod 2) :
    degree f < Fintype.card ι ↔
      Even (Finset.univ.filter (fun x => f x = 1)).card := by
  simpa [degree, anf_eval] using
    totalDegree_lt_card_iff_even_support (anf f) (anf_degreeOf_le_one f)

/-- A four-point support in three Boolean coordinates has no cubic term, as
used in the height-two paragraph of the proof of Lemma 6.4. -/
theorem degree_lt_three_of_support_card_eq_four
    (f : (Fin 3 → ZMod 2) → ZMod 2)
    (hf : (Finset.univ.filter (fun x => f x = 1)).card = 4) : degree f < 3 := by
  have h : Even (Finset.univ.filter (fun x => f x = 1)).card := by
    rw [hf]
    exact ⟨2, rfl⟩
  simpa using (degree_lt_card_iff_even_support f).mpr h

end
end BinaryFieldCounterexamples.BooleanFunctions
