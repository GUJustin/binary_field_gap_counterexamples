/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.LinearAlgebra.Lagrange
/-!
# Polynomial descent through a saturated finite image

If a polynomial map has image `D`, its degree times `|D|` exhausts the field
size, and a smaller-than-field-degree polynomial is constant on its fibers,
then it is literally a composition through that map. Interpolation on `D`
constructs the descended polynomial; degree bounds turn equality of functions
on the field into equality of polynomials.
-/
@[expose] public section
open Polynomial
namespace BinaryFieldCounterexamples
variable {B : Type*} [Field B] [Fintype B]
/-- A fiber-invariant polynomial of degree below the field size descends
through a positive-degree map whose finite image saturates the degree bound.
The output has strict degree below the image cardinality. -/
theorem polynomial_descent_of_fibers (A G : B[X]) (D : Finset B)
    (hD : D.Nonempty) (hA : 0 < A.natDegree)
    (hcard : D.card * A.natDegree = Fintype.card B)
    (hrange : ∀ y, y ∈ D ↔ ∃ x : B, A.eval x = y)
    (hfiber : ∀ x y : B, A.eval x = A.eval y → G.eval x = G.eval y)
    (hG : G.natDegree < Fintype.card B) :
    ∃ H : B[X], H.natDegree < D.card ∧ H.comp A = G := by
  classical
  have hex (y : D) : ∃ x : B, A.eval x = y := (hrange y).mp y.property
  let r : D → B := fun y => G.eval (Classical.choose (hex y))
  let H := Lagrange.interpolate (Finset.univ : Finset D) (fun y : D => (y : B)) r
  have hdeg : H.natDegree < D.card := by
    have hd := Lagrange.degree_interpolate_lt r (s := (Finset.univ : Finset D))
      (v := fun y : D => (y : B)) Subtype.val_injective.injOn
    by_cases hz : H = 0
    · rw [hz, natDegree_zero]
      exact Finset.card_pos.mpr hD
    · apply (natDegree_lt_iff_degree_lt hz).mpr
      simpa only [Finset.card_univ, Fintype.card_coe] using hd
  refine ⟨H, hdeg, ?_⟩
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
  · intro x
    rw [eval_comp]
    have hy : A.eval x ∈ D := (hrange _).mpr ⟨x, rfl⟩
    have he := Lagrange.eval_interpolate_at_node r
      (s := (Finset.univ : Finset D)) (v := fun y : D => (y : B))
      Subtype.val_injective.injOn (i := ⟨A.eval x, hy⟩) (Finset.mem_univ _)
    change H.eval (A.eval x) = G.eval x
    rw [he]
    exact hfiber _ _ (Classical.choose_spec (hex ⟨A.eval x, hy⟩))
  · rw [max_lt_iff]
    refine ⟨?_, hG⟩
    rw [natDegree_comp]
    exact (Nat.mul_lt_mul_of_pos_right hdeg hA).trans_eq hcard
end BinaryFieldCounterexamples
