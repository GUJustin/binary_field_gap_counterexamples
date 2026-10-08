/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Parameters
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.Group.Subgroup.Finite
public import BinaryFieldCounterexamples.Agreement.Basic
/-!
# The full-field example after Lemma 5.5

For a full-field domain every field element is a Gold label. Its canonical
functional polynomial is the finite Frobenius sum representing the trace
of `ω² x`, including equality as polynomials outside the domain.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The full-field example after Lemma 5.5: the binary functional `x ↦ Tr(ω²x)`. -/
noncomputable def fullFieldTraceFunctional (ω : B) : (⊤ : AddSubgroup B) →+ ZMod 2 :=
  { toFun := fun x ↦ Algebra.trace (ZMod 2) B (ω^2 * (x : B))
    map_zero' := by simp
    map_add' := by intro x y; simp [mul_add] }
/-- The full-field example after Lemma 5.5: the displayed finite trace polynomial. -/
noncomputable def fullFieldTracePolynomial (m : ℕ) (ω : B) : B[X] :=
  ∑ i ∈ Finset.range m, C (ω^(2^(i+1))) * X^(2^i)
/-- The full-field example after Lemma 5.5: the displayed polynomial evaluates to `Tr(ω²x)`. -/
theorem fullFieldTracePolynomial_eval (m : ℕ) (hB : Nat.card B = 2^m) (ω x : B) :
    (fullFieldTracePolynomial m ω).eval x = algebraMap (ZMod 2) B (Algebra.trace (ZMod 2) B (ω^2*x)) := by
  have hdim : Module.finrank (ZMod 2) B = m := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B)
    rw [hB, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hdim, Nat.card_eq_fintype_card, ZMod.card]
  simp only [fullFieldTracePolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, ← pow_mul, pow_succ]
  congr 2
  omega
/-- The full-field example after Lemma 5.5: the finite Frobenius sum is the unique functional interpolant. -/
theorem fullFieldTracePolynomial_eq_functionalPolynomial (m : ℕ) (hB : Nat.card B = 2^m) (ω : B) :
    fullFieldTracePolynomial m ω = functionalPolynomial (⊤ : AddSubgroup B) (fullFieldTraceFunctional ω) := by
  have hc : Nat.card (⊤ : AddSubgroup B) = Nat.card B :=
    Nat.card_congr (show (⊤ : AddSubgroup B) ≃ B from
      ⟨Subtype.val, fun x ↦ ⟨x, by simp⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩)
  apply eq_functionalPolynomial
  · rw [hc, hB]
    apply (degree_sum_le _ _).trans_lt
    apply Finset.sup_lt_iff (WithBot.bot_lt_coe _)|>.mpr
    intro i hi
    apply (degree_mul_le _ _).trans_lt
    have hp : 2^i < 2^m := Nat.pow_lt_pow_right (by decide) (Finset.mem_range.mp hi)
    calc
      (C (ω^(2^(i+1)))).degree + (X^(2^i) : B[X]).degree ≤ ((2^i : ℕ) : WithBot ℕ) := by
        rw [degree_X_pow]
        simpa only [zero_add] using add_le_add (degree_C_le (a := ω^(2^(i+1)))) (le_refl ((2^i : ℕ) : WithBot ℕ))
      _ < ((2^m : ℕ) : WithBot ℕ) := by exact_mod_cast hp
  · intro x
    exact fullFieldTracePolynomial_eval m hB ω x.val
/-- The full-field example after Lemma 5.5: the linear coefficient of the trace polynomial is `ω²`. -/
theorem fullFieldTracePolynomial_coeff_one (m : ℕ) (hm : 0 < m) (ω : B) :
    (fullFieldTracePolynomial m ω).coeff 1 = ω^2 := by
  classical
  rw [fullFieldTracePolynomial, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp only [pow_zero, zero_add, pow_one, coeff_C_mul, coeff_X_one, mul_one]
  · intro i hi hi0
    have hp : (2:ℕ)^i ≠ 1 := by
      intro he
      apply hi0
      exact Nat.pow_right_injective (by decide : 1 < 2) (he.trans (pow_zero 2).symm)
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right (Ne.symm hp), mul_zero]
  · simp [hm]
/-- The full-field example after Lemma 5.5: the trace functional has precisely the label `ω`. -/
theorem fullFieldTraceFunctional_parameter (m : ℕ) (hB : Nat.card B = 2^m) (ω : B) :
    functionalParameter (⊤ : AddSubgroup B) (fullFieldTraceFunctional ω) = ω := by
  have hm : 0 < m := by
    have hc : 1 < Nat.card B := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    by_contra h
    have hz : m=0 := by omega
    rw [hz, pow_zero] at hB
    omega
  apply (frobeniusEquiv B 2).injective
  change functionalParameter (⊤ : AddSubgroup B) (fullFieldTraceFunctional ω)^2 = ω^2
  rw [functionalParameter_sq, ← fullFieldTracePolynomial_eq_functionalPolynomial m hB ω,
    fullFieldTracePolynomial_coeff_one m hm ω]
/-- The full-field example after Lemma 5.5: the entire ambient field is the label space. -/
theorem parameterDomain_top : parameterDomain (⊤ : AddSubgroup B) = ⊤ := by
  classical
  apply AddSubgroup.eq_top_of_card_eq
  rw [card_parameterDomain]
  exact Nat.card_congr (show (⊤ : AddSubgroup B) ≃ B from
    ⟨Subtype.val, fun x ↦ ⟨x, by simp⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩)
/-- The full-field example after Lemma 5.5, assembled: `ℓω` is the displayed
 Frobenius polynomial and evaluates to `Tr(ω²x)`; the label space is all of `B`. -/
theorem parameterPolynomial_full_field (m : ℕ) (hB : Nat.card B = 2^m)
    (ω : parameterDomain (⊤ : AddSubgroup B)) :
    parameterPolynomial (⊤ : AddSubgroup B) ω =
        ∑ i ∈ Finset.range m, C ((ω:B)^(2^(i+1))) * X^(2^i) ∧
      (∀ x : B, (parameterPolynomial (⊤ : AddSubgroup B) ω).eval x =
        algebraMap (ZMod 2) B (Algebra.trace (ZMod 2) B ((ω:B)^2*x))) ∧
      parameterDomain (⊤ : AddSubgroup B) = ⊤ := by
  have he : parameterEquiv (⊤ : AddSubgroup B) (fullFieldTraceFunctional (ω:B)) = ω := by
    apply Subtype.ext
    exact fullFieldTraceFunctional_parameter m hB (ω:B)
  have hp : parameterPolynomial (⊤ : AddSubgroup B) ω = fullFieldTracePolynomial m (ω:B) := by
    calc
      parameterPolynomial (⊤ : AddSubgroup B) ω =
          parameterPolynomial (⊤ : AddSubgroup B) (parameterEquiv (⊤ : AddSubgroup B) (fullFieldTraceFunctional (ω:B))) := congrArg _ he.symm
      _ = functionalPolynomial (⊤ : AddSubgroup B) (fullFieldTraceFunctional (ω:B)) := parameterPolynomial_apply _ _
      _ = fullFieldTracePolynomial m (ω:B) := (fullFieldTracePolynomial_eq_functionalPolynomial m hB (ω:B)).symm
  exact ⟨hp, fun x ↦ hp ▸ fullFieldTracePolynomial_eval m hB (ω:B) x, parameterDomain_top⟩
/-- The full-field example after Lemma 5.5 contrasts with general domains:
 a binary line containing a nonzero element whose cube is not one differs from
 its label space. This gives a concrete sufficient condition, rather than
 asserting that every proper domain has a different label space. -/
theorem parameterDomain_ne_of_cube_ne_one (D : AddSubgroup B) [Fintype D]
    (hD : Nat.card D = 2) (a : B) (ha : a ∈ D) (hne : a ≠ 0) (hcube : a^3 ≠ 1) :
    parameterDomain D ≠ D := by
  intro he
  let c : parameterDomain D := ⟨a, by rw [he]; exact ha⟩
  let l := (parameterEquiv D).symm c
  have hd : (parameterPolynomial D c).natDegree ≤ 1 := by
    have hd := (parameterPolynomial_support_and_degree D c).2
    change (parameterPolynomial D c).natDegree ≤ Nat.card D / 2 at hd
    rw [hD] at hd
    exact hd
  have hp : parameterPolynomial D c = C (a^2)*X := by
    rw [eq_X_add_C_of_natDegree_le_one hd, parameterPolynomial_coeff_one]
    have hz : (parameterPolynomial D c).coeff 0 = 0 := functionalPolynomial_coeff_zero D l
    rw [hz, C_0, add_zero]
  have hv := functionalPolynomial_eval D l ⟨a,ha⟩
  change (parameterPolynomial D c).eval a = algebraMap (ZMod 2) B (l ⟨a,ha⟩) at hv
  rw [hp, eval_mul, eval_C, eval_X, ← pow_succ] at hv
  rcases binary_eq_zero_or_one (l ⟨a,ha⟩) with hzero | hone
  · rw [hzero, map_zero] at hv
    exact hne ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hv)
  · rw [hone, map_one] at hv
    exact hcube hv
/-- The prose after Lemma 5.5, with a witnessed domain: every binary field
 of cardinality at least eight contains a binary line that differs from its
 Gold label space. Thus the general-domain distinction is an actual existence
 statement, while the full-field example has equal domain and label space. -/
theorem exists_domain_ne_parameterDomain (hB : 8 ≤ Nat.card B) :
    ∃ D : AddSubgroup B, Nat.card D = 2 ∧ parameterDomain D ≠ D := by
  classical
  have hex : ∃ a : B, a ≠ 0 ∧ a^3 ≠ 1 := by
    by_contra h
    push Not at h
    let P : B[X] := X^4-X
    have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero B (by decide : 1 < 4)
    have hdeg : P.natDegree = 4 := FiniteField.X_pow_card_sub_X_natDegree_eq B (by decide : 1 < 4)
    have hall : ∀ x : B, P.eval x = 0 := by
      intro x
      by_cases hx : x=0
      · simp [P,hx]
      · have hc := h x hx
        simp only [P,eval_sub,eval_pow,eval_X]
        rw [show x^4=x^3*x from pow_succ x 3,hc,one_mul,sub_self]
    have hc := card_filter_eval_eq_zero_le (Finset.univ : Finset B) P hP
    have he : Finset.univ.filter (fun x : B ↦ P.eval x=0) = Finset.univ := by
      ext x; simp [hall]
    rw [he,Finset.card_univ,hdeg] at hc
    rw [Nat.card_eq_fintype_card] at hB
    omega
  obtain ⟨a,hne,hcube⟩ := hex
  let D : AddSubgroup B :=
    { carrier := {x | x=0 ∨ x=a}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro x y (rfl | rfl) (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]
      neg_mem' := by
        rintro x (rfl | rfl) <;> simp [CharTwo.neg_eq] }
  have hD : Nat.card D=2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have he : Finset.univ.filter (fun x : B ↦ x ∈ D) = {0,a} := by
      ext x; simp [D]
    rw [he]
    exact Finset.card_pair hne.symm
  refine ⟨D,hD,parameterDomain_ne_of_cube_ne_one D hD a ?_ hne hcube⟩
  exact Or.inr rfl
end BinaryFieldCounterexamples.Gold
