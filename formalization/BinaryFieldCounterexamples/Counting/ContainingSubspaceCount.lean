/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.QuotientIncidence

/-!
# Exact counts of subspaces containing a fixed subspace

The quotient correspondence preserves the shifted dimension. Combining it
with the actual finite-field subspace count yields the expected Gaussian
coefficient without assuming a counting law.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Module
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]

/-- Subspaces of dimension `e` containing `U` correspond to subspaces of
shifted dimension in the quotient by `U`. -/
noncomputable def containingSubspacesQuotientEquiv (U : Submodule k V) (e : ℕ)
    (hUe : Module.finrank k U ≤ e) :
    {W : Submodule k V // U ≤ W ∧ Module.finrank k W = e} ≃
      subspacesOfFinrank k (V ⧸ U) (e - Module.finrank k U) := by
  exact {
    toFun := fun W => ⟨W.val.map U.mkQ, by
      have h := QuadraticGeometry.quotientMap_finrank_add U W.val W.property.1
      rw [W.property.2] at h
      omega⟩
    invFun := fun T => ⟨T.val.comap U.mkQ, Submodule.le_comap_mkQ U T.val, by
      have h := QuadraticGeometry.quotientComap_finrank_add U T.val
      rw [T.property] at h
      omega⟩
    left_inv := fun W => by
      apply Subtype.ext
      simpa only [Submodule.comap_map_mkQ] using sup_eq_right.mpr W.property.1
    right_inv := fun T => by
      apply Subtype.ext
      exact Submodule.map_comap_eq_self (by simp) }

/-- Exact Gaussian count of fixed-dimensional subspaces containing a prescribed subspace. -/
theorem containingSubspaces_card_eq_gaussianBinomial (U : Submodule k V) (e : ℕ)
    (hUe : Module.finrank k U ≤ e) (heV : e ≤ Module.finrank k V) :
    Nat.card {W : Submodule k V // U ≤ W ∧ Module.finrank k W = e} =
      gaussianBinomial (Fintype.card k)
        (Module.finrank k V - Module.finrank k U)
        (e - Module.finrank k U) := by
  rw [Nat.card_congr (containingSubspacesQuotientEquiv U e hUe)]
  have hquot : Module.finrank k (V ⧸ U) =
      Module.finrank k V - Module.finrank k U := by
    have h := U.finrank_quotient_add_finrank
    omega
  have hle : e - Module.finrank k U ≤ Module.finrank k (V ⧸ U) := by
    rw [hquot]
    omega
  rw [subspacesOfFinrank_card_eq_gaussianBinomial _ hle, hquot]

end BinaryFieldCounterexamples
