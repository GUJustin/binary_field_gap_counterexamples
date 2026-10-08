/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplane
public import BinaryFieldCounterexamples.Polynomial.FiniteImageDescent
/-!
# Literal polynomial descent to a prescribed hyperplane

The degree-q map onto a prescribed scalar hyperplane has derivative one and
saturates the finite-image degree bound. Any polynomial of degree below the
extension-field size which is constant on its scalar-line fibers therefore
descends literally, with strict degree below the hyperplane size. Its derivative
also descends by the chain rule. Sparse support bounds are subsequent results.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
set_option linter.unusedSectionVars false

/-- The actual map polynomial has derivative one in the scalar characteristic. -/
theorem hyperplanePolynomial_derivative (v : B) :
    (hyperplanePolynomial (k := k) v).derivative = 1 := by
  have hq : (Fintype.card k : B) = 0 := by
    rw [← map_natCast (algebraMap k B), FiniteField.cast_card_eq_zero, map_zero]
  rw [hyperplanePolynomial, derivative_sub, derivative_X, derivative_C_mul_X_pow]
  simp [hq]

/-- A codimension-one scalar subspace has index equal to the scalar-field size. -/
theorem hyperplane_card_mul (D : Submodule k B)
    (hD : Module.finrank k D + 1 = Module.finrank k B) :
    Nat.card D * Fintype.card k = Fintype.card B := by
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card,
    ← Nat.pow_succ, Nat.succ_eq_add_one, hD]
  exact (Module.card_eq_pow_finrank (K := k)).symm

/-- A polynomial constant on the scalar-line fibers descends literally to the prescribed hyperplane; the derivative identity is also literal. -/
theorem hyperplane_polynomial_descent (D : Submodule k B)
    (hD : Module.finrank k D + 1 = Module.finrank k B)
    (v : B) (hv : v ≠ 0) (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D)
    (G : B[X]) (hG : G.natDegree < Fintype.card B)
    (hfiber : ∀ x y : B, x-y ∈ Submodule.span k {v} → G.eval x = G.eval y) :
    ∃ H : B[X], H.natDegree < Nat.card D ∧
      H.comp (hyperplanePolynomial (k := k) v) = G ∧
      H.derivative.comp (hyperplanePolynomial (k := k) v) = G.derivative := by
  classical
  let S : Finset B := Finset.univ.filter (fun x => x ∈ D)
  have hS : S.card = Nat.card D := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  have hn : S.Nonempty := ⟨0, by simp [S]⟩
  obtain ⟨H, hH, he⟩ := polynomial_descent_of_fibers (hyperplanePolynomial (k := k) v) G S hn
    (by rw [hyperplanePolynomial_natDegree v hv]; exact Fintype.card_pos)
    (by rw [hS, hyperplanePolynomial_natDegree v hv]; exact hyperplane_card_mul D hD)
    (by
      intro y
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hrange]
      change (∃ x, hyperplaneMap (k := k) v x = y) ↔ _
      simp only [hyperplanePolynomial_eval v _ hv])
    (by
      intro x y hxy
      apply hfiber
      rw [← hyperplaneMap_ker v hv, LinearMap.mem_ker, map_sub, sub_eq_zero]
      simpa only [hyperplanePolynomial_eval v _ hv] using hxy) hG
  refine ⟨H, hS ▸ hH, he, ?_⟩
  have hd := congrArg Polynomial.derivative he
  rw [derivative_comp, hyperplanePolynomial_derivative, one_mul] at hd
  exact hd
end BinaryFieldCounterexamples.QuadraticFormTrace
