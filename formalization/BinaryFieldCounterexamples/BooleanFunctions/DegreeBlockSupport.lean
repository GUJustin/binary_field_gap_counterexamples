/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeProducts

/-!
# Monomial types supported in a single coordinate block

The proof of Lemma 6.5 separates mixed monomial types from terms entirely in one
block. A polynomial using coordinates of common weight `e` has no component at a
weight that is not a natural multiple of `e`. This remains true after Boolean
reduction; lower-degree terms confined to a single block cannot contribute to
the mixed types in the root-uniqueness argument.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions
open MvPolynomial

variable {R σ Γ M : Type*} [CommSemiring R] [AddCommMonoid M]

/-- A renamed polynomial lies entirely in weights that are multiples of the
common weight of its coordinate block. No injectivity assumption is needed. -/
theorem weightedHomogeneousComponent_rename_eq_zero_of_block
    (w : Γ → M) (j : σ → Γ) (e t : M) (hj : ∀ i, w (j i) = e)
    (ht : ∀ n : ℕ, n • e ≠ t) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w t (rename j p) = 0 := by
  classical
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd
  obtain ⟨a, rfl, _⟩ := coeff_rename_ne_zero j p d (mem_support_iff.mp hd)
  have hw : Finsupp.weight w (a.mapDomain j) = a.degree • e := by
    rw [Finsupp.weight_apply,
      Finsupp.sum_mapDomain_index (h := fun i c => c • w i)
        (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)]
    simp_rw [hj]
    rw [Finsupp.sum, Finset.sum_nsmul_assoc]
    rfl
  rw [hw]
  exact ht a.degree

/-- Taking a homogeneous component preserves every individual degree bound. -/
theorem homogeneousComponent_mem_restrictDegree (p : MvPolynomial σ R)
    (k m : ℕ) (hp : p ∈ restrictDegree σ R m) :
    homogeneousComponent k p ∈ restrictDegree σ R m := by
  classical
  rw [mem_restrictDegree] at hp ⊢
  intro d hd i
  rw [support_homogeneousComponent] at hd
  exact hp d (Finset.mem_filter.mp hd).1 i

/-- Boolean reduction of a polynomial confined to a block has no mixed-type component. -/
theorem weightedHomogeneousComponent_reduction_rename_eq_zero_of_block
    [Fintype σ] [Fintype Γ] (w : Γ → M) (j : σ → Γ)
    (hinj : Function.Injective j) (e t : M) (hj : ∀ i, w (j i) = e)
    (ht : ∀ n : ℕ, n • e ≠ t) (p : MvPolynomial σ (ZMod 2)) :
    weightedHomogeneousComponent w t (reduction (rename j p)) = 0 := by
  rw [reduction_rename j hinj]
  exact weightedHomogeneousComponent_rename_eq_zero_of_block w j e t hj ht (reduction p)

end BinaryFieldCounterexamples.BooleanFunctions
