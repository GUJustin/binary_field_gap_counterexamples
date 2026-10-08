/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.QuotientIncidence
/-!
# Exact counts of linear complements

A projection fixing a subspace is determined by its values on one complement.
The resulting actual equivalence with a linear-map space counts every possible
complement, supplying the lifting factor needed in subspace incidence.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Projections fixing a subspace are exactly arbitrary linear maps on a chosen complement. -/
noncomputable def projectionsEquivLinearMaps (P C : Submodule k V) (h : IsCompl P C) :
    {f : V →ₗ[k] P // ∀ x : P,f x=x} ≃ (C →ₗ[k] P) := by
  let e := P.prodEquivOfIsCompl C h
  refine {
    toFun := fun f => f.val.comp C.subtype
    invFun := fun g => ⟨((LinearMap.id : P →ₗ[k] P).coprod g).comp e.symm.toLinearMap,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    simp only [e,LinearMap.comp_apply,LinearEquiv.coe_coe,
      Submodule.prodEquivOfIsCompl_symm_apply_left,LinearMap.coprod_apply,LinearMap.id_apply,map_zero,add_zero]
  · intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    obtain ⟨⟨p,c⟩,rfl⟩ := e.surjective v
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,e.symm_apply_apply,
      LinearMap.coprod_apply,LinearMap.id_apply]
    change p+f.val c=f.val ((p : V)+(c : V))
    rw [map_add,f.property]
  · intro g
    apply LinearMap.ext
    intro c
    simp only [e,Submodule.subtype_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      Submodule.prodEquivOfIsCompl_symm_apply_right,LinearMap.coprod_apply,LinearMap.id_apply,zero_add]
/-- Actual complements are parametrized by linear maps from a chosen complement. -/
noncomputable def complementsEquivLinearMaps (P C : Submodule k V) (h : IsCompl P C) :
    {S : Submodule k V // IsCompl P S} ≃ (C →ₗ[k] P) :=
  P.isComplEquivProj.trans (projectionsEquivLinearMaps P C h)
/-- The actual complement count is the cardinality of the corresponding linear-map space. -/
theorem complements_natCard [Fintype k] [FiniteDimensional k V]
    (P C : Submodule k V) (h : IsCompl P C) :
    Nat.card {S : Submodule k V // IsCompl P S} =
      (Fintype.card k)^(Module.finrank k C*Module.finrank k P) := by
  rw [Nat.card_congr (complementsEquivLinearMaps P C h),
    Module.natCard_eq_pow_finrank (K:=k),Module.finrank_linearMap,Nat.card_eq_fintype_card]
/-- Every subspace has the expected exact number of linear complements. -/
theorem complements_natCard_eq_pow [Fintype k] [FiniteDimensional k V]
    (P : Submodule k V) :
    Nat.card {S : Submodule k V // IsCompl P S} =
      (Fintype.card k)^((Module.finrank k V-Module.finrank k P)*Module.finrank k P) := by
  obtain ⟨C,hC⟩ := P.exists_isCompl
  have hd := (P.quotientEquivOfIsCompl C hC).finrank_eq
  have hq := P.finrank_quotient_add_finrank
  have hc : Module.finrank k C=Module.finrank k V-Module.finrank k P := by omega
  rw [complements_natCard P C hC,hc]

end BinaryFieldCounterexamples
