/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularLineQuotient
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.QuotientIncidence
/-!
# Actual singular-subspace flags through a line

A totally singular subspace containing x lies in x perpendicular. Restricting to
that hyperplane and then quotienting by the literal line gives the exact
fixed-dimension correspondence needed for nonradical singular-line flags.
The correspondence itself also applies to radical singular lines.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
/-- A totally singular ambient subspace containing a vector lies in its perpendicular hyperplane. -/
theorem isotropic_le_perp (Q : QuadraticForm k V) (x : V) (S : Submodule k V)
    (hxS : x ∈ S) (hS : ∀ z ∈ S,Q z=0) : S ≤ (Q.polarBilin x).ker := by
  intro z hz
  change Q.polarBilin x z=0
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hS _ (S.add_mem hxS hz),hS _ hxS,hS _ hz]
  simp
/-- The singular line in the perpendicular hyperplane has dimension one. -/
theorem singularPerpLine_finrank (Q : QuadraticForm k V) (x : V) (hx : Q x=0) (hne : x≠0) :
    Module.finrank k (singularPerpLine Q x hx)=1 := by
  apply finrank_span_singleton
  intro h
  exact hne (congrArg Subtype.val h)
/-- Ambient singular subspaces through the line are exactly singular subspaces of its perpendicular hyperplane through that line. -/
noncomputable def singularPerpSubspaceEquiv [FiniteDimensional k V]
    (Q : QuadraticForm k V) (x : V) (hx : Q x=0) (e : ℕ) :
    {S : Submodule k V // (k ∙ x)≤S ∧ Module.finrank k S=e ∧ ∀ z ∈ S,Q z=0} ≃
      {S : Submodule k (Q.polarBilin x).ker // singularPerpLine Q x hx≤S ∧
        Module.finrank k S=e ∧ ∀ z ∈ S,(Q.comp (Q.polarBilin x).ker.subtype) z=0} := by
  refine {
    toFun := fun S => ⟨S.val.comap (Q.polarBilin x).ker.subtype,?_,?_,?_⟩
    invFun := fun S => ⟨S.val.map (Q.polarBilin x).ker.subtype,?_,?_,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [singularPerpLine,Submodule.span_singleton_le_iff_mem]
    exact S.property.1 (Submodule.mem_span_singleton_self x)
  · have hle := isotropic_le_perp Q x S.val
      (S.property.1 (Submodule.mem_span_singleton_self x)) S.property.2.2
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,S.property.2.1]
  · intro z hz; exact S.property.2.2 z.val hz
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨⟨x,polar_self_of_singular Q x hx⟩,
      S.property.1 (Submodule.mem_span_singleton_self _),rfl⟩
  · rw [Submodule.finrank_map_subtype_eq,S.property.2.1]
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact S.property.2.2 w hw
  · intro S
    apply Subtype.ext
    change (S.val.comap (Q.polarBilin x).ker.subtype).map (Q.polarBilin x).ker.subtype=S.val
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (isotropic_le_perp Q x S.val
      (S.property.1 (Submodule.mem_span_singleton_self x)) S.property.2.2)
  · intro S
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective _) S.val
/-- Actual ambient singular (e+1)-spaces through a nonzero singular line correspond to singular e-spaces in its literal quotient. -/
noncomputable def singularLineFlagQuotientEquiv [FiniteDimensional k V]
    (Q : QuadraticForm k V) (x : V) (hx : Q x=0) (hne : x≠0) (e : ℕ) :
    {S : Submodule k V // (k ∙ x)≤S ∧ Module.finrank k S=e+1 ∧ ∀ z ∈ S,Q z=0} ≃
      {T : Submodule k ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx) //
        Module.finrank k T=e ∧ ∀ z ∈ T,
          (Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
            (singularPerpLine_le_radical Q x hx) z=0} := by
  let eqv := isotropicQuotientDimensionEquiv (Q.comp (Q.polarBilin x).ker.subtype)
    (singularPerpLine Q x hx) (singularPerpLine_le_radical Q x hx) e
  have he := singularPerpLine_finrank Q x hx hne
  rw [he] at eqv
  exact (singularPerpSubspaceEquiv Q x hx (e+1)).trans eqv.symm
end BinaryFieldCounterexamples.QuadraticGeometry
