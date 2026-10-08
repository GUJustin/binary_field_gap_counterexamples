/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.ComplementCount
/-!
# Subspace lifts with a prescribed radical intersection

Complements in a quotient count the subspaces having a fixed intersection
with a given subspace and a fixed image in its quotient. The exact power of
the field cardinality supplies the lifting factor in degenerate quadratic
form incidence counts.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Complementarity in a quotient is the prescribed intersection and full sum upstairs. -/
theorem isCompl_quotient_iff (A R : Submodule k V) (hAR : A≤R)
    (T : Submodule k (V ⧸ A)) :
    IsCompl (R.map A.mkQ) T ↔ R ⊓ T.comap A.mkQ=A ∧ R ⊔ T.comap A.mkQ=⊤ := by
  let e := A.comapMkQRelIso
  have he : e (R.map A.mkQ)=⟨R,hAR⟩ := by
    apply Subtype.ext
    change (R.map A.mkQ).comap A.mkQ=R
    rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hAR]
  rw [e.isCompl_iff,he,isCompl_iff,disjoint_iff,codisjoint_iff]
  simp only [Subtype.ext_iff]
  rfl
/-- Actual quotient complements correspond to subspaces with prescribed intersection and sum. -/
noncomputable def quotientComplementEquiv (A R : Submodule k V) (hAR : A≤R) :
    {T : Submodule k (V ⧸ A) // IsCompl (R.map A.mkQ) T} ≃
      {S : Submodule k V // R ⊓ S=A ∧ R ⊔ S=⊤} := by
  refine {
    toFun := fun T => ⟨T.val.comap A.mkQ,(isCompl_quotient_iff A R hAR T.val).mp T.property⟩
    invFun := fun S => ⟨S.val.map A.mkQ,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (isCompl_quotient_iff A R hAR _).mpr
    have hAS : A≤S.val := S.property.1.ge.trans inf_le_right
    rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hAS]
    exact S.property
  · intro T
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)
  · intro S
    apply Subtype.ext
    change (S.val.map A.mkQ).comap A.mkQ=S.val
    have hAS : A≤S.val := S.property.1.ge.trans inf_le_right
    rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hAS]

/-- Count subspaces with fixed intersection with a given subspace and full sum. -/
theorem quotient_complement_natCard [Fintype k] [FiniteDimensional k V]
    (A R : Submodule k V) (hAR : A≤R) :
    Nat.card {S : Submodule k V // R ⊓ S=A ∧ R ⊔ S=⊤} =
      (Fintype.card k)^((Module.finrank k V-Module.finrank k R)*
        (Module.finrank k R-Module.finrank k A)) := by
  rw [←Nat.card_congr (quotientComplementEquiv A R hAR),complements_natCard_eq_pow]
  have hr := QuadraticGeometry.quotientMap_finrank_add A R hAR
  have hv := A.finrank_quotient_add_finrank
  have he1 : Module.finrank k (R.map A.mkQ)=Module.finrank k R-Module.finrank k A := by omega
  have he2 : Module.finrank k (V ⧸ A)-Module.finrank k (R.map A.mkQ)=
      Module.finrank k V-Module.finrank k R := by omega
  rw [he2,he1]

/-- Transport the complement problem inside an ambient subspace to its interval of subspaces. -/
noncomputable def intervalComplementEquiv (A R U : Submodule k V)
    (hAR : A≤R) (hRU : R≤U) :
    {S : Submodule k U // (R.comap U.subtype) ⊓ S=A.comap U.subtype ∧
      (R.comap U.subtype) ⊔ S=⊤} ≃
      {S : Submodule k V // R ⊓ S=A ∧ R ⊔ S=U} := by
  have hAU := hAR.trans hRU
  refine {
    toFun := fun S => ⟨S.val.map U.subtype,?_,?_⟩
    invFun := fun S => ⟨S.val.comap U.subtype,?_,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have he := congrArg (Submodule.map U.subtype) S.property.1
    rw [Submodule.map_inf U.subtype U.subtype_injective,Submodule.map_comap_subtype,
      inf_eq_right.mpr hRU,Submodule.map_comap_subtype,inf_eq_right.mpr hAU] at he
    exact he
  · have he := congrArg (Submodule.map U.subtype) S.property.2
    rw [Submodule.map_sup,Submodule.map_comap_subtype,inf_eq_right.mpr hRU,
      Submodule.map_top,Submodule.range_subtype] at he
    exact he
  · rw [←Submodule.comap_inf,S.property.1]
  · have hSU : S.val≤U := le_sup_right.trans S.property.2.le
    apply Submodule.map_injective_of_injective U.subtype_injective
    rw [Submodule.map_sup,Submodule.map_comap_subtype,inf_eq_right.mpr hRU,
      Submodule.map_comap_subtype,inf_eq_right.mpr hSU,Submodule.map_top,Submodule.range_subtype]
    exact S.property.2
  · intro S
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective U.subtype_injective S.val
  · intro S
    apply Subtype.ext
    change (S.val.comap U.subtype).map U.subtype=S.val
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (le_sup_right.trans S.property.2.le)

/-- Count subspaces with both intersection and sum prescribed. -/
theorem interval_complement_natCard [Fintype k] [FiniteDimensional k V]
    (A R U : Submodule k V) (hAR : A≤R) (hRU : R≤U) :
    Nat.card {S : Submodule k V // R ⊓ S=A ∧ R ⊔ S=U} =
      (Fintype.card k)^((Module.finrank k U-Module.finrank k R)*
        (Module.finrank k R-Module.finrank k A)) := by
  rw [←Nat.card_congr (intervalComplementEquiv A R U hAR hRU),
    quotient_complement_natCard _ _ (Submodule.comap_mono hAR),
    (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe (hAR.trans hRU)).finrank_eq]

/-- A prescribed quotient image is equivalent to a prescribed sum with the kernel. -/
theorem map_quotient_eq_iff_sup (R S : Submodule k V) (T : Submodule k (V ⧸ R)) :
    S.map R.mkQ=T ↔ R ⊔ S=T.comap R.mkQ := by
  constructor
  · intro h
    rw [←h,Submodule.comap_map_mkQ]
  · intro h
    apply Submodule.comap_injective_of_surjective R.mkQ_surjective
    rw [Submodule.comap_map_mkQ]
    exact h

/-- The exact number of lifts of a quotient subspace with a prescribed kernel intersection. -/
theorem quotient_lift_fiber_natCard [Fintype k] [FiniteDimensional k V]
    (A R : Submodule k V) (hAR : A≤R) (T : Submodule k (V ⧸ R)) :
    Nat.card {S : Submodule k V // R ⊓ S=A ∧ S.map R.mkQ=T} =
      (Fintype.card k)^(Module.finrank k T*(Module.finrank k R-Module.finrank k A)) := by
  let e : {S : Submodule k V // R ⊓ S=A ∧ S.map R.mkQ=T} ≃
      {S : Submodule k V // R ⊓ S=A ∧ R ⊔ S=T.comap R.mkQ} :=
    Equiv.subtypeEquivRight (fun S => and_congr Iff.rfl (map_quotient_eq_iff_sup R S T))
  rw [Nat.card_congr e,interval_complement_natCard A R _ hAR (Submodule.le_comap_mkQ R T)]
  have hd := QuadraticGeometry.quotientComap_finrank_add R T
  have he : Module.finrank k (T.comap R.mkQ)-Module.finrank k R=Module.finrank k T := by omega
  rw [he]

end BinaryFieldCounterexamples
