/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Coordinates
public import Mathlib.FieldTheory.ChevalleyWarning
/-!
# Isotropic vectors over finite fields

The actual upper-coordinate quadratic polynomial has total degree at most two.
Chevalley–Warning makes a unique zero impossible in dimension greater than two,
without a restriction on the field characteristic.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open MvPolynomial
attribute [local instance] Classical.decEq upperIndexFintype
set_option linter.unusedSectionVars false
variable {k : Type*} [Field k] [Fintype k]
/-- The literal multivariate polynomial of an actual quadratic form. -/
noncomputable def quadraticPolynomial (d : ℕ) (Q : QuadraticForm k (Fin d → k)) :
    MvPolynomial (Fin d) k :=
  ∑ p : UpperIndex d, C (upperCoordinates d Q p) * (X p.val.1 * X p.val.2)
/-- The literal polynomial evaluates to the actual quadratic form. -/
theorem quadraticPolynomial_eval (d : ℕ) (Q : QuadraticForm k (Fin d → k)) (x : Fin d → k) :
    eval x (quadraticPolynomial d Q) = Q x := by
  rw [← ofUpperCoordinates_upperCoordinates d Q, ofUpperCoordinates_apply]
  simp [quadraticPolynomial, upperCoordinates_ofUpperCoordinates]
/-- Every actual quadratic coordinate polynomial has total degree at most two. -/
theorem quadraticPolynomial_totalDegree (d : ℕ) (Q : QuadraticForm k (Fin d → k)) :
    (quadraticPolynomial d Q).totalDegree ≤ 2 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro p hp
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  exact (totalDegree_mul _ _).trans (by simp)
/-- A quadratic form in more than two finite-field coordinates has a nonzero zero. -/
theorem quadraticForm_exists_nonzero_zero (p d : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k (Fin d → k)) (hd : 2 < d) :
    ∃ x, x ≠ 0 ∧ Q x = 0 := by
  by_contra hn
  have hQ : ∀ x, Q x=0 → x=0 := by
    intro x hx
    by_contra hne
    exact hn ⟨x,hne,hx⟩
  have heval : ∀ x, eval x (quadraticPolynomial d Q)=0 ↔ x=0 := by
    intro x
    rw [quadraticPolynomial_eval]
    exact ⟨hQ x,by rintro rfl; exact Q.map_zero⟩
  have hh := char_dvd_card_solutions (K:=k) p (f:=quadraticPolynomial d Q)
    ((quadraticPolynomial_totalDegree d Q).trans_lt (by simpa using hd))
  have hcard : Fintype.card {x : Fin d → k // eval x (quadraticPolynomial d Q)=0}=1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0,(heval 0).mpr rfl⟩,?_⟩
    intro x
    apply Subtype.ext
    exact (heval x.val).mp x.property
  rw [hcard] at hh
  exact (Fact.out : p.Prime).not_dvd_one hh

/-- Basis transport gives a nonzero singular vector in every dimension greater than two. -/
theorem quadraticForm_exists_nonzero_zero_of_finrank
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V)
    (hd : 2 < Module.finrank k V) : ∃ x, x ≠ 0 ∧ Q x=0 := by
  let e := (Module.finBasis k V).equivFun.symm
  obtain ⟨x,hx,hQ⟩ := quadraticForm_exists_nonzero_zero p (Module.finrank k V)
    (Q.comp e.toLinearMap) hd
  refine ⟨e x,?_,hQ⟩
  intro he
  apply hx
  exact e.injective (by simpa using he)

/-- An anisotropic quadratic space over a finite field has dimension at most two. -/
theorem anisotropic_finrank_le_two
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V)
    (hQ : Q.Anisotropic) : Module.finrank k V ≤ 2 := by
  by_contra hd
  obtain ⟨x,hx,hzero⟩ := quadraticForm_exists_nonzero_zero_of_finrank p Q (by omega)
  exact hx (hQ x hzero)

end BinaryFieldCounterexamples.QuadraticCoordinates
