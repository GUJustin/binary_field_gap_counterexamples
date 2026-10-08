/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalQuotient
/-!
# Actual singular lines and zero-vector counts

Every nonzero singular vector lies on one actual one-dimensional totally
singular subspace. Its fiber has q−1 vectors, giving the exact projective
singular-line count without assuming a rank/type classification.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Actual one-dimensional subspaces on which the quadratic form vanishes. -/
def SingularLines (Q : QuadraticForm k V) :=
  {L : Submodule k V // Module.finrank k L=1 ∧ ∀ x ∈ L, Q x=0}
/-- A quadratic zero generates a totally singular line. -/
theorem quadratic_zero_on_span (Q : QuadraticForm k V) (x : V) (hx : Q x=0) :
    ∀ y ∈ Submodule.span k {x}, Q y=0 := by
  intro y hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [Q.map_smul,hx,smul_zero]
/-- The actual singular line spanned by a nonzero singular vector. -/
noncomputable def singularLineOfVector (Q : QuadraticForm k V) (x : V) (hx : x≠0) (hQ : Q x=0) :
    SingularLines Q :=
  ⟨Submodule.span k {x},finrank_span_singleton hx,quadratic_zero_on_span Q x hQ⟩
/-- A nonzero vector of an actual singular line recovers that line. -/
theorem singularLineOfVector_eq [FiniteDimensional k V] (Q : QuadraticForm k V) (L : SingularLines Q)
    (x : L.val) (hx : x≠0) :
    singularLineOfVector Q x.val (by simpa using hx) (L.property.2 x.val x.property)=L := by
  apply Subtype.ext
  change Submodule.span k {x.val}=L.val
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by intro y hy; rw [Set.mem_singleton_iff] at hy; subst y; exact x.property)
  · rw [finrank_span_singleton (by simpa using hx),L.property.1]

/-- Nonzero singular vectors are the disjoint union of nonzero vectors on singular lines. -/
noncomputable def singularVectorEquiv [FiniteDimensional k V] (Q : QuadraticForm k V) :
    {x : V // x≠0 ∧ Q x=0} ≃ Σ L : SingularLines Q, {x : L.val // x≠0} := by
  let f : (Σ L : SingularLines Q, {x : L.val // x≠0}) → {x : V // x≠0 ∧ Q x=0} :=
    fun y => ⟨y.2.val.val,by simpa using y.2.property,y.1.property.2 _ y.2.val.property⟩
  apply Equiv.symm
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨L,x,hx⟩ ⟨M,y,hy⟩ h
    have hv : x.val=y.val := congrArg Subtype.val h
    have hLM : L=M := by
      rw [←singularLineOfVector_eq Q L x hx,←singularLineOfVector_eq Q M y hy]
      congr 1
    subst M
    have hxy : x=y := Subtype.ext hv
    subst y
    rfl
  · intro x
    refine ⟨⟨singularLineOfVector Q x.val x.property.1 x.property.2,
      ⟨⟨x.val,Submodule.mem_span_singleton_self x.val⟩,?_⟩⟩,rfl⟩
    intro he
    exact x.property.1 (congrArg Subtype.val he)
/-- Each actual singular line contributes exactly q−1 nonzero zeros. -/
theorem singularLines_card_mul [Fintype k] [Fintype V] (Q : QuadraticForm k V) :
    Nat.card {x : V // Q x=0}-1 = Nat.card (SingularLines Q)*(Fintype.card k-1) := by
  classical
  let : Fintype (Submodule k V) := Fintype.ofInjective (fun L : Submodule k V => (L : Set V)) SetLike.coe_injective
  let : Fintype (SingularLines Q) := by unfold SingularLines; exact Fintype.ofFinite _
  have hz : Nat.card {x : V // x≠0 ∧ Q x=0} = Nat.card {x : V // Q x=0}-1 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have he : Finset.univ.filter (fun x : V => x≠0 ∧ Q x=0) =
        (Finset.univ.filter (fun x : V => Q x=0)).erase 0 := by
      ext x
      simp
    rw [he,Finset.card_erase_of_mem (by simp)]
  rw [←hz,Nat.card_congr (singularVectorEquiv Q),Nat.card_sigma]
  have hf (L : SingularLines Q) : Nat.card {x : L.val // x≠0}=Fintype.card k-1 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique]
    rw [Module.card_eq_pow_finrank (K:=k),L.property.1,pow_one]
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

/-- The number of actual singular lines is the expected quotient of the nonzero zero count. -/
theorem singularLines_card [Fintype k] [Fintype V] (Q : QuadraticForm k V) :
    Nat.card (SingularLines Q) = (Nat.card {x : V // Q x=0}-1)/(Fintype.card k-1) := by
  rw [singularLines_card_mul,Nat.mul_div_cancel]
  exact Nat.sub_pos_of_lt Fintype.one_lt_card

end BinaryFieldCounterexamples.QuadraticGeometry
