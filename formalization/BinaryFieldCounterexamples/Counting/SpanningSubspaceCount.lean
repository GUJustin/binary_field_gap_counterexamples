/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.QuotientComplementCount
public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
/-!
# Exact count of subspaces spanning with a prescribed subspace

A subspace spanning with `H` is specified by its intersection with `H` and
a complement in the quotient by that intersection. The actual equivalence
below gives the Gaussian intersection count times the exact complement count.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Finite V]

omit [Fintype k] in
/-- Prescribing the intersection and full sum forces the subspace dimension. -/
theorem spanning_finrank_of_intersection (H A W : Submodule k V)
    (hinter : H ⊓ W = A) (hsup : H ⊔ W = ⊤) :
    finrank k W + finrank k H = finrank k V + finrank k A := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq H W
  rw [hinter, hsup, finrank_top] at h
  omega

/-- Spanning subspaces split into their intersection and a quotient complement. -/
noncomputable def spanningSubspaceEquiv (H : Submodule k V) (d r w : ℕ)
    (hd : finrank k V = d) (hH : finrank k H = d-r) (hrw : r ≤ w) (hwd : w ≤ d) :
    (Σ A : subspacesOfFinrank k H (w-r),
      {W : Submodule k V // H ⊓ W = A.val.map H.subtype ∧ H ⊔ W = ⊤}) ≃
      {W : Submodule k V // finrank k W = w ∧ H ⊔ W = ⊤} := by
  let : Module.Finite k V := Module.Finite.of_finite
  let f := fun (z : Σ A : subspacesOfFinrank k H (w-r),
      {W : Submodule k V // H ⊓ W = A.val.map H.subtype ∧ H ⊔ W = ⊤}) =>
    (⟨z.2.val, by
      have h := spanning_finrank_of_intersection H _ z.2.val z.2.property.1 z.2.property.2
      rw [hd,hH,Submodule.finrank_map_subtype_eq,z.1.property] at h
      omega, z.2.property.2⟩ : {W : Submodule k V // finrank k W = w ∧ H ⊔ W = ⊤})
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨A,W⟩ ⟨A',W'⟩ he
    have hW : W.val = W'.val := congrArg Subtype.val he
    have hA : A = A' := by
      apply Subtype.ext
      apply Submodule.map_injective_of_injective H.subtype_injective
      rw [←W.property.1,←W'.property.1,hW]
    subst A'
    have hWW : W = W' := Subtype.ext hW
    subst W'
    rfl
  · intro W
    let A := (H ⊓ W.val).comap H.subtype
    have hA : A.map H.subtype = H ⊓ W.val := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr inf_le_left
    have hdim : finrank k A = w-r := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq H W.val
      rw [W.property.2,finrank_top,hd,hH,W.property.1,←hA,
        Submodule.finrank_map_subtype_eq] at h
      omega
    exact ⟨⟨⟨A,hdim⟩,⟨W.val,hA.symm,W.property.2⟩⟩,rfl⟩

/-- Exact count of `w`-subspaces whose sum with a codimension-`r` subspace is all of `V`. -/
theorem spanningSubspaces_natCard (H : Submodule k V) (d r w : ℕ)
    (hd : finrank k V = d) (hH : finrank k H = d-r) (hrw : r ≤ w) (hwd : w ≤ d) :
    Nat.card {W : Submodule k V // finrank k W = w ∧ H ⊔ W = ⊤} =
      (Fintype.card k)^(r*(d-w)) * gaussianBinomial (Fintype.card k) (d-r) (w-r) := by
  classical
  let : Module.Finite k V := Module.Finite.of_finite
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (Submodule k V) := Fintype.ofFinite _
  let : Fintype (Submodule k H) := Fintype.ofFinite _
  have hf (A : subspacesOfFinrank k H (w-r)) :
      Nat.card {W : Submodule k V // H ⊓ W = A.val.map H.subtype ∧ H ⊔ W = ⊤} =
        (Fintype.card k)^(r*(d-w)) := by
    rw [quotient_complement_natCard _ H (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact y.property),hd,hH,Submodule.finrank_map_subtype_eq,A.property]
    congr 2 <;> omega
  rw [←Nat.card_congr (spanningSubspaceEquiv H d r w hd hH hrw hwd),Nat.card_sigma]
  simp only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,subspacesOfFinrank_card_eq_gaussianBinomial (w-r) (by rw [hH]; omega),hH]
  exact Nat.mul_comm _ _
end BinaryFieldCounterexamples
