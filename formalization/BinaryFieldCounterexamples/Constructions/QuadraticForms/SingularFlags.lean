/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularLines
/-!
# Actual singular line–subspace flag counts

Restriction identifies singular lines inside an actual subspace. Counting the
same flags in the two orders gives the singular-line recurrence's incidence
factor, with concrete spaces and exact finite cardinalities.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Singular lines in a restricted form are precisely ambient singular lines contained in the subspace. -/
noncomputable def singularLinesInSubspaceEquiv (Q : QuadraticForm k V) (S : Submodule k V) :
    SingularLines (Q.comp S.subtype) ≃ {L : SingularLines Q // L.val≤S} := by
  refine {
    toFun := fun L => ⟨⟨L.val.map S.subtype,?_,?_⟩,?_⟩
    invFun := fun L => ⟨L.val.val.comap S.subtype,?_,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective L.val).finrank_eq.symm.trans L.property.1
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact L.property.2 y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact y.property
  · exact (Submodule.comapSubtypeEquivOfLe L.property).finrank_eq.trans L.val.property.1
  · intro x hx
    exact L.val.property.2 x.val hx
  · intro L
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective S.subtype_injective L.val
  · intro L
    apply Subtype.ext
    apply Subtype.ext
    change (L.val.val.comap S.subtype).map S.subtype=L.val.val
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr L.property
/-- A totally singular subspace contains the expected number of actual singular lines. -/
theorem singularLinesInSubspace_card [Fintype k] [Fintype V]
    (Q : QuadraticForm k V) (S : Submodule k V) (hS : ∀ x ∈ S,Q x=0) :
    Nat.card {L : SingularLines Q // L.val≤S} =
      ((Fintype.card k)^(Module.finrank k S)-1)/(Fintype.card k-1) := by
  rw [←Nat.card_congr (singularLinesInSubspaceEquiv Q S),singularLines_card]
  have hzv (x : S) : (Q.comp S.subtype) x=0 := hS x.val x.property
  have hz : Nat.card {x : S // (Q.comp S.subtype) x=0}=Nat.card S := by
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype,hzv]
  rw [hz,Module.natCard_eq_pow_finrank (K:=k),Nat.card_eq_fintype_card]

/-- Actual totally singular subspaces of a specified dimension. -/
def TotallySingularSubspaces (Q : QuadraticForm k V) (e : ℕ) :=
  {S : Submodule k V // Module.finrank k S=e ∧ ∀ x ∈ S,Q x=0}
/-- The actual finite type of singular lines. -/
noncomputable def singularLinesFintype [Fintype V] (Q : QuadraticForm k V) : Fintype (SingularLines Q) := by
  classical
  let : Fintype (Submodule k V) := Fintype.ofInjective (fun L : Submodule k V => (L : Set V)) SetLike.coe_injective
  unfold SingularLines
  exact Fintype.ofFinite _
/-- The actual finite type of fixed-dimensional totally singular subspaces. -/
noncomputable def totallySingularSubspacesFintype [Fintype V] (Q : QuadraticForm k V) (e : ℕ) :
    Fintype (TotallySingularSubspaces Q e) := by
  classical
  let : Fintype (Submodule k V) := Fintype.ofInjective (fun L : Submodule k V => (L : Set V)) SetLike.coe_injective
  unfold TotallySingularSubspaces
  exact Fintype.ofFinite _
attribute [local instance] singularLinesFintype totallySingularSubspacesFintype
/-- Swap the two orders of choosing an actual singular line–subspace flag. -/
noncomputable def singularFlagsEquiv (Q : QuadraticForm k V) (e : ℕ) :
    (Σ S : TotallySingularSubspaces Q e, {L : SingularLines Q // L.val≤S.val}) ≃
      (Σ L : SingularLines Q, {S : TotallySingularSubspaces Q e // L.val≤S.val}) := by
  refine {
    toFun := fun z => ⟨z.2.val,⟨z.1,z.2.property⟩⟩
    invFun := fun z => ⟨z.2.val,⟨z.1,z.2.property⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨S,L,hL⟩; rfl
  · rintro ⟨L,S,hS⟩; rfl

/-- Double-counting actual singular flags gives the exact line-incidence factor. -/
theorem singular_flag_count [Fintype k] [Fintype V] (Q : QuadraticForm k V) (e : ℕ) :
    (∑ L : SingularLines Q, Nat.card {S : TotallySingularSubspaces Q e // L.val≤S.val}) =
      Nat.card (TotallySingularSubspaces Q e) * (((Fintype.card k)^e-1)/(Fintype.card k-1)) := by
  have hf (S : TotallySingularSubspaces Q e) :
      Nat.card {L : SingularLines Q // L.val≤S.val}=((Fintype.card k)^e-1)/(Fintype.card k-1) := by
    rw [singularLinesInSubspace_card Q S.val S.property.2,S.property.1]
  rw [←Nat.card_sigma,Nat.card_congr (singularFlagsEquiv Q e).symm,Nat.card_sigma]
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end BinaryFieldCounterexamples.QuadraticGeometry
