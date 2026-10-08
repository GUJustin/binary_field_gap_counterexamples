/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplane
public import Mathlib.GroupTheory.Coset.Basic
/-!
# Exact fiber counts for hyperplane descent

A predicate pulled back along a surjective linear map has one kernel-sized fiber
over each satisfying image point. Applied to the actual hyperplane map, whose
kernel is the scalar line through its nonzero parameter, this multiplies counts
by the scalar-field size. The polynomial specialization applies to any descended
polynomial, including its derivative, without assumptions on its roots.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
/-- A predicate pulled back by a surjective linear map consists of one kernel-sized
fiber over each point satisfying the predicate. -/
noncomputable def linearPredicateFiberEquiv (f : V →ₗ[k] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    {x : V // P (f x)} ≃ (LinearMap.ker f) × {y : W // P y} := by
  classical
  let s : W → V := fun y => Classical.choose (hf y)
  have hs (y : W) : f (s y) = y := Classical.choose_spec (hf y)
  refine {
    toFun := fun x => (⟨x.1 - s (f x.1), by simp [LinearMap.mem_ker, hs]⟩,
      ⟨f x.1, x.2⟩)
    invFun := fun z => ⟨z.1.1 + s z.2.1, by simpa [map_add, hs, z.1.2] using z.2.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp
  · rintro ⟨a, y⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [map_add, hs]
    · apply Subtype.ext
      simp [map_add, hs]
/-- The exact cardinality of the inverse image of any predicate. -/
theorem linearPredicate_natCard (f : V →ₗ[k] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    Nat.card {x : V // P (f x)} = Nat.card (LinearMap.ker f) * Nat.card {y : W // P y} := by
  rw [Nat.card_congr (linearPredicateFiberEquiv f hf P), Nat.card_prod]
variable {B : Type*} [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- Every fiber of the hyperplane map has exactly the scalar-field size. -/
theorem hyperplaneMap_kernel_natCard (v : B) (hv : v ≠ 0) :
    Nat.card (LinearMap.ker (hyperplaneMap (k := k) v)) = Fintype.card k := by
  rw [hyperplaneMap_ker v hv, Module.natCard_eq_pow_finrank (K := k),
    finrank_span_singleton hv, pow_one, Nat.card_eq_fintype_card]
/-- Exact predicate counting on any prescribed image of the hyperplane map. -/
theorem hyperplaneMap_predicate_natCard (v : B) (hv : v ≠ 0)
    (D : Submodule k B) (hD : LinearMap.range (hyperplaneMap (k := k) v) = D)
    (P : B → Prop) :
    Nat.card {x : B // P (hyperplaneMap (k := k) v x)} =
      Fintype.card k * Nat.card {y : D // P y.1} := by
  let f : B →ₗ[k] D := (hyperplaneMap (k := k) v).codRestrict D
    (fun x => hD ▸ LinearMap.mem_range_self _ x)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (show y.1 ∈ LinearMap.range (hyperplaneMap (k := k) v) by
      rw [hD]; exact y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hker : LinearMap.ker f = LinearMap.ker (hyperplaneMap (k := k) v) := by
    ext x
    simp [f, LinearMap.mem_ker]
  change Nat.card {x : B // P (f x).1} = _
  rw [linearPredicate_natCard f hf (fun y => P y.1), hker,
    hyperplaneMap_kernel_natCard v hv]
/-- Polynomial composition with the hyperplane map multiplies the number of
zeros on its image by exactly the scalar-field size. -/
theorem hyperplanePolynomial_zero_natCard (v : B) (hv : v ≠ 0)
    (D : Submodule k B) (hD : LinearMap.range (hyperplaneMap (k := k) v) = D)
    (H : Polynomial B) :
    Nat.card {x : B // (H.comp (hyperplanePolynomial (k := k) v)).eval x = 0} =
      Fintype.card k * Nat.card {y : D // H.eval y.1 = 0} := by
  simpa only [Polynomial.eval_comp, hyperplanePolynomial_eval v _ hv] using
    hyperplaneMap_predicate_natCard v hv D hD (fun x => H.eval x = 0)
end BinaryFieldCounterexamples.QuadraticFormTrace
