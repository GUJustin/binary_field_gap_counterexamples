/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.Data.Finsupp.Order

/-!
# Algebraic normal forms of Boolean functions

This is the reduced multilinear representative used in Section 6.2 after
[Definition 6.2, p. 59](../../../binary-field-counterexamples.pdf#page=59)
(translation periods and essential coordinates). Boolean functions and balance
are defined in Definition 3.14, p. 25. Evaluation identifies reduced polynomials
over `ZMod 2` with all Boolean functions. Explicitly capping every positive
monomial exponent at one preserves evaluation and never increases total degree.
The latter fact is the foundation for the affine invariance and quotient clauses
of Lemma 6.4 (tree structure).
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial

open scoped Classical

variable {σ : Type*} [Fintype σ]

/-- Every Boolean function has a reduced representative. -/
theorem exists_reduced (f : (σ → ZMod 2) → ZMod 2) :
    ∃ p : MvPolynomial σ (ZMod 2), p ∈ restrictDegree σ (ZMod 2) 1 ∧
      (∀ x, eval x p = f x) := by
  have h : f ∈ (restrictDegree σ (ZMod 2) (Fintype.card (ZMod 2) - 1)).map
      (evalₗ (ZMod 2) σ) := by
    rw [map_restrict_dom_evalₗ]
    trivial
  obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp h
  exact ⟨p, hp, congrFun he⟩

/-- The unique reduced multilinear polynomial representing a Boolean function. -/
def anf (f : (σ → ZMod 2) → ZMod 2) : MvPolynomial σ (ZMod 2) :=
  Classical.choose (exists_reduced f)

/-- Every coordinate in the normal form has exponent at most one. -/
theorem anf_mem_restrictDegree (f : (σ → ZMod 2) → ZMod 2) :
    anf f ∈ restrictDegree σ (ZMod 2) 1 := by
  exact (Classical.choose_spec (exists_reduced f)).1

/-- Evaluation of the normal form recovers the original function. -/
@[simp] theorem anf_eval (f : (σ → ZMod 2) → ZMod 2) (x : σ → ZMod 2) :
    eval x (anf f) = f x := by
  exact (Classical.choose_spec (exists_reduced f)).2 x

/-- Reduced representatives with the same evaluations are equal. -/
theorem anf_unique (f : (σ → ZMod 2) → ZMod 2) (p : MvPolynomial σ (ZMod 2))
    (hp : p ∈ restrictDegree σ (ZMod 2) 1) (he : ∀ x, eval x p = f x) :
    anf f = p := by
  let e := Fintype.equivFin σ
  have hzero : rename e (anf f - p) = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero
    · intro x
      rw [eval_rename]
      simp [he]
    · change rename e (anf f - p) ∈ restrictDegree (Fin (Fintype.card σ)) (ZMod 2) 1
      rw [mem_restrictDegree]
      intro d hd i
      have hi : degreeOf (e (e.symm i)) (rename e (anf f - p)) ≤ 1 := by
        rw [degreeOf_rename_of_injective e.injective]
        apply degreeOf_le_iff.mpr
        intro m hm
        exact (mem_restrictDegree σ _ 1).mp
          ((restrictDegree σ (ZMod 2) 1).sub_mem (anf_mem_restrictDegree f) hp) m hm _
      simpa using degreeOf_le_iff.mp hi d hd
  apply sub_eq_zero.mp
  exact (rename_injective e e.injective) (by simpa using hzero)

/-- Reinterpreting a reduced polynomial as a function recovers the polynomial. -/
@[simp] theorem anf_eval_eq_of_reduced (p : MvPolynomial σ (ZMod 2))
    (hp : p ∈ restrictDegree σ (ZMod 2) 1) :
    anf (fun x => eval x p) = p := by
  exact anf_unique _ p hp (fun _ => rfl)

/-- The normal form has degree at most one in each coordinate. -/
theorem anf_degreeOf_le_one (f : (σ → ZMod 2) → ZMod 2) (i : σ) :
    (anf f).degreeOf i ≤ 1 := by
  exact degreeOf_le_iff.mpr ((mem_restrictDegree σ _ 1).mp (anf_mem_restrictDegree f) · · i)

/-- Normal forms commute with pointwise addition. -/
@[simp] theorem anf_add (f g : (σ → ZMod 2) → ZMod 2) :
    anf (f + g) = anf f + anf g := by
  apply anf_unique
  · exact (restrictDegree σ (ZMod 2) 1).add_mem
      (anf_mem_restrictDegree f) (anf_mem_restrictDegree g)
  · intro x
    simp

/-- The normal form of a constant is its constant polynomial. -/
@[simp] theorem anf_const (c : ZMod 2) : anf (fun _ : σ → ZMod 2 => c) = C c := by
  apply anf_unique
  · exact (restrictTotalDegree_le_restrictDegree σ (ZMod 2) 1)
      ((mem_restrictTotalDegree σ 1 _).mpr (by simp))
  · simp

omit [Fintype σ] in
/-- Cap every positive exponent at one, as required for Boolean reduction. -/
def cappedExponent (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => if n = 0 then 0 else 1) (by simp)

omit [Fintype σ] in
@[simp] theorem cappedExponent_apply (d : σ →₀ ℕ) (i : σ) :
    cappedExponent d i = if d i = 0 then 0 else 1 := by
  rfl

omit [Fintype σ] in
/-- Exponent capping gives a reduced monomial. -/
theorem capped_monomial_mem_restrictDegree (d : σ →₀ ℕ) (c : ZMod 2) :
    monomial (cappedExponent d) c ∈ restrictDegree σ (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro s hs i
  have hs' : s = cappedExponent d := by
    have := support_monomial_subset hs
    simpa using this
  subst s
  simp only [cappedExponent_apply]
  split_ifs <;> omega

/-- Exponent capping cannot increase the sum of exponents. -/
theorem cappedExponent_sum_le (d : σ →₀ ℕ) :
    (cappedExponent d).sum (fun _ n => n) ≤ d.sum (fun _ n => n) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro i _
  simp only [cappedExponent_apply]
  split_ifs <;> omega

/-- Exponent capping preserves evaluations on the binary cube. -/
theorem eval_capped_monomial (d : σ →₀ ℕ) (c : ZMod 2) (x : σ → ZMod 2) :
    eval x (monomial (cappedExponent d) c) = eval x (monomial d c) := by
  rw [eval_monomial, eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cappedExponent_apply]
  by_cases h : d i = 0
  · simp [h]
  · have hx : x i = 0 ∨ x i = 1 := by
      have hh := (x i).val_lt
      interval_cases hv : (x i).val <;> [left; right] <;>
        apply ZMod.val_injective <;> simp [hv, ZMod.val_one_eq_one_mod]
    rcases hx with hx | hx <;> simp [h, hx]

/-- Reduce an arbitrary polynomial to its Boolean algebraic normal form. -/
def reduction (p : MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  anf (fun x => eval x p)

/-- Reduction of a monomial caps its exponents at one. -/
@[simp] theorem reduction_monomial (d : σ →₀ ℕ) (c : ZMod 2) :
    reduction (monomial d c) = monomial (cappedExponent d) c := by
  apply anf_unique
  · exact capped_monomial_mem_restrictDegree d c
  · exact fun x => eval_capped_monomial d c x

/-- Reduced expansion of a polynomial, with the original coefficients. -/
theorem reduction_eq_sum (p : MvPolynomial σ (ZMod 2)) :
    reduction p = ∑ d ∈ p.support, monomial (cappedExponent d) (p.coeff d) := by
  apply anf_unique
  · exact Submodule.sum_mem _ fun d _ => capped_monomial_mem_restrictDegree d _
  · intro x
    rw [map_sum]
    simp_rw [eval_capped_monomial]
    conv_rhs => rw [p.as_sum]
    rw [map_sum]

/-- Passing to algebraic normal form never raises total degree. -/
theorem reduction_totalDegree_le (p : MvPolynomial σ (ZMod 2)) :
    (reduction p).totalDegree ≤ p.totalDegree := by
  rw [reduction_eq_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_monomial_le _ _).trans
    ((cappedExponent_sum_le d).trans (le_totalDegree hd))

/-- Multiplication of functions is polynomial multiplication followed by reduction. -/
theorem anf_mul (f g : (σ → ZMod 2) → ZMod 2) :
    anf (f * g) = reduction (anf f * anf g) := by
  unfold reduction
  congr 1
  funext x
  simp

omit [Fintype σ] in
/-- A variable outside the image of an injective renaming is absent. -/
theorem degreeOf_rename_of_not_mem_range {τ : Type*} (j : σ → τ)
    (hj : Function.Injective j) (p : MvPolynomial σ (ZMod 2))
    (i : τ) (hi : i ∉ Set.range j) :
    (rename j p).degreeOf i = 0 := by
  rw [degreeOf, degrees_rename_of_injective hj, Multiset.count_eq_zero]
  intro h
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
  exact hi ⟨a, ha⟩

omit [Fintype σ] in
/-- Injective coordinate renaming preserves the multilinear degree bound. -/
theorem rename_mem_restrictDegree {τ : Type*} (j : σ → τ)
    (hj : Function.Injective j) (p : MvPolynomial σ (ZMod 2))
    (hp : p ∈ restrictDegree σ (ZMod 2) 1) :
    rename j p ∈ restrictDegree τ (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro d hd i
  have hb : (rename j p).degreeOf i ≤ 1 := by
    by_cases hi : i ∈ Set.range j
    · obtain ⟨a, rfl⟩ := hi
      rw [degreeOf_rename_of_injective hj]
      exact degreeOf_le_iff.mpr (fun m hm => (mem_restrictDegree σ p 1).mp hp m hm a)
    · rw [degreeOf_rename_of_not_mem_range j hj p i hi]
      omega
  exact degreeOf_le_iff.mp hb d hd

omit [Fintype σ] in
/-- Multiplying a multilinear polynomial by a fresh coordinate stays multilinear. -/
theorem mul_X_mem_restrictDegree (p : MvPolynomial σ (ZMod 2)) (i : σ)
    (hp : p ∈ restrictDegree σ (ZMod 2) 1) (hi : p.degreeOf i = 0) :
    p * X i ∈ restrictDegree σ (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro d hd j
  have hb : (p * X i).degreeOf j ≤ 1 := by
    by_cases hij : j = i
    · subst j
      exact (degreeOf_mul_le i p (X i)).trans (by simp [hi])
    · rw [degreeOf_mul_X_of_ne p hij]
      exact degreeOf_le_iff.mpr (fun m hm => (mem_restrictDegree σ p 1).mp hp m hm j)
  exact degreeOf_le_iff.mp hb d hd

omit [Fintype σ] in
/-- Left multiplication by a fresh coordinate stays multilinear. -/
theorem X_mul_mem_restrictDegree (p : MvPolynomial σ (ZMod 2)) (i : σ)
    (hp : p ∈ restrictDegree σ (ZMod 2) 1) (hi : p.degreeOf i = 0) :
    X i * p ∈ restrictDegree σ (ZMod 2) 1 := by
  rw [mul_comm]
  exact mul_X_mem_restrictDegree p i hp hi

/-- Evaluation is unchanged by Boolean reduction. -/
@[simp] theorem reduction_eval (p : MvPolynomial σ (ZMod 2)) (x : σ → ZMod 2) :
    eval x (reduction p) = eval x p := by
  exact anf_eval _ x

/-- Boolean reduction commutes with polynomial addition. -/
@[simp] theorem reduction_add (p q : MvPolynomial σ (ZMod 2)) :
    reduction (p + q) = reduction p + reduction q := by
  unfold reduction
  rw [show (fun x => eval x (p + q)) =
    (fun x => eval x p) + (fun x => eval x q) by funext x; simp]
  exact anf_add _ _

/-- Boolean reduction commutes with an injective change of variable names. -/
theorem reduction_rename {τ : Type*} [Fintype τ] (j : σ → τ)
    (hj : Function.Injective j) (p : MvPolynomial σ (ZMod 2)) :
    reduction (rename j p) = rename j (reduction p) := by
  apply anf_unique
  · exact rename_mem_restrictDegree j hj _ (anf_mem_restrictDegree _)
  · intro x
    simp only [eval_rename, reduction_eval]

omit [Fintype σ] in
/-- Products of reduced polynomials with disjoint variable supports stay reduced. -/
theorem mul_mem_restrictDegree_of_disjoint (p q : MvPolynomial σ (ZMod 2))
    (hp : p ∈ restrictDegree σ (ZMod 2) 1)
    (hq : q ∈ restrictDegree σ (ZMod 2) 1)
    (hdisjoint : ∀ i, p.degreeOf i = 0 ∨ q.degreeOf i = 0) :
    p * q ∈ restrictDegree σ (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro d hd i
  have hpi : p.degreeOf i ≤ 1 :=
    degreeOf_le_iff.mpr (fun m hm => (mem_restrictDegree σ p 1).mp hp m hm i)
  have hqi : q.degreeOf i ≤ 1 :=
    degreeOf_le_iff.mpr (fun m hm => (mem_restrictDegree σ q 1).mp hq m hm i)
  have hi : (p * q).degreeOf i ≤ 1 :=
    (degreeOf_mul_le i p q).trans (by rcases hdisjoint i with h | h <;> omega)
  exact degreeOf_le_iff.mp hi d hd

end BinaryFieldCounterexamples.BooleanFunctions
