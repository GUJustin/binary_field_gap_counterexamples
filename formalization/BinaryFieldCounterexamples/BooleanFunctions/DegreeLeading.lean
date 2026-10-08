/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.Degree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Leading terms and Boolean reduction

The proof of Lemma 6.5 (unique root functional, Section 6.2) ignores all terms
below the children's leading degree when detecting the degree of their product
with a linear form. These lemmas justify that operation, including reduction
by `Xᵢ² = Xᵢ`.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
/-- Removing the homogeneous part of degree `k` leaves degree strictly below
`k`, whenever `k` is positive and the polynomial had degree at most `k`. -/
theorem totalDegree_sub_homogeneousComponent_lt (p : MvPolynomial σ (ZMod 2))
    {k : ℕ} (hk : 0 < k) (hp : p.totalDegree ≤ k) :
    (p - homogeneousComponent k p).totalDegree < k := by
  classical
  rw [totalDegree, Finset.sup_lt_iff hk]
  intro d hd
  by_contra hn
  have hk' : k ≤ d.sum (fun _ e => e) := Nat.le_of_not_gt hn
  have hz : (p - homogeneousComponent k p).coeff d = 0 := by
    rw [coeff_sub, coeff_homogeneousComponent]
    change p.coeff d - (if d.sum (fun _ e => e) = k then p.coeff d else 0) = 0
    by_cases he : d.sum (fun _ e => e) = k
    · simp [he]
    · have hgt : p.totalDegree < d.sum (fun _ e => e) := by omega
      have hc := coeff_eq_zero_of_totalDegree_lt hgt
      simp [hc]
  exact (mem_support_iff.mp hd) hz

/-- Only the leading part of the second factor can contribute in degree `k+1`
after multiplication by a polynomial of degree at most one and Boolean reduction. -/
theorem homogeneousComponent_reduction_mul_top
    (l p : MvPolynomial σ (ZMod 2)) {k : ℕ} (hk : 0 < k)
    (hl : l.totalDegree ≤ 1) (hp : p.totalDegree ≤ k) :
    homogeneousComponent (k + 1) (reduction (l * p)) =
      homogeneousComponent (k + 1) (reduction (l * homogeneousComponent k p)) := by
  have hr := totalDegree_sub_homogeneousComponent_lt p hk hp
  have hlow : (reduction (l * (p - homogeneousComponent k p))).totalDegree < k + 1 := by
    have hmul := (reduction_totalDegree_le (l * (p - homogeneousComponent k p))).trans
      (totalDegree_mul l (p - homogeneousComponent k p))
    omega
  have he : l * p = l * homogeneousComponent k p + l * (p - homogeneousComponent k p) := by
    ring
  rw [he, reduction_add, map_add, homogeneousComponent_eq_zero _ _ hlow, add_zero]

end BinaryFieldCounterexamples.BooleanFunctions
