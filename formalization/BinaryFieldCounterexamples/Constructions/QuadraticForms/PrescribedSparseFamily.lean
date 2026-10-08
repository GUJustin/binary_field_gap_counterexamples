/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SparseFamilyPopulation
/-!
# Sparse locator families on the prescribed scalar domain

The full-field and hyperplane constructions share one dimension-indexed
interface, keeping the literal prescribed submodule and exact Gaussian count.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- Both allowed codimensions keep all sparse factor witnesses on the original domain. -/
theorem prescribed_sparse_locator_family
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n h t : ℕ) (hh : h≤1) (ht : 2≤t) (htn : t≤n-h)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B)
    (hDcard : (Finset.univ.filter (fun x : B => x∈D)).card=(Fintype.card k)^(2*n-h)) :
    let S := Finset.univ.filter (fun x : B => x∈D)
    let d := 2*n-h
    let L := subspacePolynomial D.toAddSubgroup
    let R := primePowerQuarterNumerator p r L 0
    ∃ E : Finset B[X],
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) (n-h) t/(Fintype.card k-1)≤E.card ∧
      ∀ P∈E, ∃ A : B[X], A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(d-t-1) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (S.filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(d-2*t) ∧
        (P-R).degree<(Fintype.card k)^(d-2) ∧
        (S.filter (fun x : B => P.eval x=0)).card=
          (Fintype.card k)^(d-1)-(Fintype.card k-1)*(Fintype.card k)^(d-t-1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with rfl | rfl
  · have hS : Finset.univ.filter (fun x : B => x∈D)=Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp only [Finset.card_univ,hDcard,Nat.sub_zero,hcard]
      exact le_refl _
    have htop : D=⊤ := by
      apply top_unique
      intro x hx
      have hm : x∈Finset.univ.filter (fun y : B => y∈D) := by rw [hS]; exact Finset.mem_univ x
      exact (Finset.mem_filter.mp hm).2
    subst D
    simpa only [Nat.sub_zero,Submodule.mem_top,Finset.filter_true] using
      fullfield_sparse_locator_family p r hr hq n t ht (by simpa using htn) hcard
  · simpa only [show 2*n-1-t-1=2*n-t-2 by omega,
      show 2*n-1-2*t=2*n-2*t-1 by omega,
      show 2*n-1-2=2*n-3 by omega,
      show 2*n-1-1=2*n-2 by omega] using
      hyperplane_sparse_locator_family p r hr hq n t ht htn hcard D hDcard
end BinaryFieldCounterexamples.QuadraticFormTrace
