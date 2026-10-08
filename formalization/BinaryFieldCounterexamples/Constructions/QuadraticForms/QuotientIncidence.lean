/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalQuotient
/-!
# Actual isotropic-subspace correspondence through radical quotients

Map and comap preserve vanishing for quotients by a subspace of the quadratic
radical. Rank-nullity supplies the exact dimension shift, giving an actual
bijection of fixed-dimension totally singular subspaces. No counting formula
or rank/type classification is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- A radical-contained quotient map preserves total singularity of an actual subspace. -/
theorem isotropic_map_quotient_iff (Q : QuadraticForm k V)
    (N S : Submodule k V) (hN : N ≤ Q.radical) :
    (∀ x ∈ S.map N.mkQ, Q.lift N hN x=0) ↔ (∀ x ∈ S, Q x=0) := by
  constructor
  · intro h x hx
    exact h (N.mkQ x) ⟨x,hx,rfl⟩
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact h x hx

/-- A quotient subspace is totally singular exactly when its full preimage is. -/
theorem isotropic_comap_quotient_iff (Q : QuadraticForm k V)
    (N : Submodule k V) (hN : N ≤ Q.radical) (T : Submodule k (V ⧸ N)) :
    (∀ x ∈ T.comap N.mkQ, Q x=0) ↔ (∀ x ∈ T, Q.lift N hN x=0) := by
  constructor
  · intro h y hy
    obtain ⟨x,rfl⟩ := N.mkQ_surjective y
    exact h x hy
  · intro h x hx
    exact h (N.mkQ x) hx
/-- Actual totally singular quotient subspaces correspond to those containing the quotient kernel. -/
noncomputable def isotropicQuotientEquiv (Q : QuadraticForm k V)
    (N : Submodule k V) (hN : N ≤ Q.radical) :
    {T : Submodule k (V ⧸ N) // ∀ x ∈ T,Q.lift N hN x=0} ≃
      {S : Submodule k V // N≤S ∧ ∀ x ∈ S,Q x=0} := by
  refine {
    toFun := fun T => ⟨T.val.comap N.mkQ,Submodule.le_comap_mkQ N T.val,
      (isotropic_comap_quotient_iff Q N hN T.val).mpr T.property⟩
    invFun := fun S => ⟨S.val.map N.mkQ,(isotropic_map_quotient_iff Q N S.val hN).mpr S.property.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro T
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)
  · intro S
    apply Subtype.ext
    simpa only [Submodule.comap_map_mkQ] using sup_eq_right.mpr S.property.1

/-- The dimension of a subspace containing the quotient kernel drops by that kernel dimension. -/
theorem quotientMap_finrank_add [FiniteDimensional k V]
    (N S : Submodule k V) (hNS : N≤S) :
    Module.finrank k (S.map N.mkQ)+Module.finrank k N=Module.finrank k S := by
  have h := (N.mkQ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,LinearMap.ker_domRestrict,Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hNS).finrank_eq] at h
  exact h

/-- The full quotient preimage adds exactly the kernel dimension. -/
theorem quotientComap_finrank_add [FiniteDimensional k V]
    (N : Submodule k V) (T : Submodule k (V ⧸ N)) :
    Module.finrank k T+Module.finrank k N=Module.finrank k (T.comap N.mkQ) := by
  have h := quotientMap_finrank_add N (T.comap N.mkQ) (Submodule.le_comap_mkQ N T)
  rw [Submodule.map_comap_eq_self (by simp)] at h
  exact h

/-- The actual totally singular correspondence preserves the precise shifted dimension. -/
noncomputable def isotropicQuotientDimensionEquiv [FiniteDimensional k V]
    (Q : QuadraticForm k V) (N : Submodule k V) (hN : N ≤ Q.radical) (e : ℕ) :
    {T : Submodule k (V ⧸ N) // Module.finrank k T=e ∧ ∀ x ∈ T,Q.lift N hN x=0} ≃
      {S : Submodule k V // N≤S ∧ Module.finrank k S=e+Module.finrank k N ∧ ∀ x ∈ S,Q x=0} := by
  refine {
    toFun := fun T => ⟨T.val.comap N.mkQ,Submodule.le_comap_mkQ N T.val,?_,
      (isotropic_comap_quotient_iff Q N hN T.val).mpr T.property.2⟩
    invFun := fun S => ⟨S.val.map N.mkQ,?_,(isotropic_map_quotient_iff Q N S.val hN).mpr S.property.2.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [←quotientComap_finrank_add,T.property.1]
  · have h := quotientMap_finrank_add N S.val S.property.1
    rw [S.property.2.1] at h
    omega
  · intro T
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)
  · intro S
    apply Subtype.ext
    simpa only [Submodule.comap_map_mkQ] using sup_eq_right.mpr S.property.1

end BinaryFieldCounterexamples.QuadraticGeometry
