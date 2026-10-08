/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianIdentities
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.SetLike.Fintype

/-!
# Exact finite-field subspace counts

Independent frames split explicitly into a subspace and an ordered basis.
Combining this equivalence with the proved frame and general-linear-group
cardinalities yields the integral Gaussian count of fixed-dimensional
subspaces over every finite field.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Finite V]

/-- Subspaces of a fixed dimension. -/
abbrev subspacesOfFinrank (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (e : ℕ) := {W : Submodule k V // Module.finrank k W = e}

theorem basis_heq_of_submodule_eq {ι : Type*} {W₁ W₂ : Submodule k V}
    (hW : W₁ = W₂) (b₁ : Basis ι k W₁) (b₂ : Basis ι k W₂)
    (hb : ∀ i, (b₁ i : V) = b₂ i) : HEq b₁ b₂ := by
  subst W₂
  apply heq_of_eq
  ext i
  exact hb i

/-- Independent frames split into their span and a basis of that span. -/
noncomputable def independentFramesEquivSubspaceBasis (e : ℕ) :
    {v : Fin e → V // LinearIndependent k v} ≃
      Σ W : subspacesOfFinrank k V e, Basis (Fin e) k W.val := by
  exact {
    toFun := fun v => ⟨⟨Submodule.span k (Set.range v.val), by
      rw [finrank_span_eq_card v.property, Fintype.card_fin]⟩, Basis.span v.property⟩
    invFun := fun p => ⟨fun i => (p.2 i : V), p.2.linearIndependent.map'
    p.1.val.subtype (LinearMap.ker_eq_bot.mpr p.1.val.injective_subtype)⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext i
      simp
    right_inv := fun p => by
      rcases p with ⟨W,b⟩
      unfold subspacesOfFinrank at W
      have hspan : Submodule.span k (Set.range (fun i => (b i : V))) = W.val := by
        have hrange : Set.range (fun i => (b i : V)) =
            W.val.subtype '' Set.range b := by
          ext x
          constructor
          · rintro ⟨i,rfl⟩
            exact ⟨b i,⟨i,rfl⟩,rfl⟩
          · rintro ⟨y,⟨i,rfl⟩,rfl⟩
            exact ⟨i,rfl⟩
        rw [hrange, Submodule.span_image]
        change (Submodule.span k (Set.range b)).map W.val.subtype = W.val
        rw [b.span_eq, Submodule.map_top]
        exact Submodule.range_subtype W.val
      have hfirst :
          (⟨Submodule.span k (Set.range (fun i => (b i : V))), by
            rw [finrank_span_eq_card]
            · exact Fintype.card_fin e
            · exact b.linearIndependent.map' W.val.subtype
                (LinearMap.ker_eq_bot.mpr W.val.injective_subtype)⟩ :
              subspacesOfFinrank k V e) = W := by
        apply Subtype.ext
        exact hspan
      apply Sigma.ext hfirst
      exact basis_heq_of_submodule_eq hspan _ _ (fun i => by simp) }

/-- Bases indexed by a finite type are the same data as coordinate equivalences. -/
noncomputable def basisEquivCoordinateEquiv {ι W : Type*} [Finite ι]
    [AddCommGroup W] [Module k W] :
    Basis ι k W ≃ (W ≃ₗ[k] ι → k) := by
  exact {
    toFun := fun b => b.equivFun
    invFun := fun e => Basis.ofEquivFun e
    left_inv := Basis.ofEquivFun_equivFun
    right_inv := Basis.equivFun_ofEquivFun }

noncomputable def finiteSubmoduleFintype : Fintype (Submodule k V) := Fintype.ofFinite _

noncomputable def subspacesOfFinrankFintype (e : ℕ) :
    Fintype (subspacesOfFinrank k V e) := Fintype.ofFinite _

noncomputable def subspaceCarrierFintype {e : ℕ} (W : subspacesOfFinrank k V e) :
    Fintype W.val := Fintype.ofFinite _

attribute [local instance] finiteSubmoduleFintype
attribute [local instance] subspacesOfFinrankFintype
attribute [local instance] subspaceCarrierFintype

noncomputable def coordinateLinearEquivFintype {e : ℕ}
    (W : subspacesOfFinrank k V e) : Fintype (W.val ≃ₗ[k] Fin e → k) :=
  Fintype.ofInjective (fun f : W.val ≃ₗ[k] Fin e → k => (f : W.val → Fin e → k))
    LinearEquiv.coe_injective

attribute [local instance] coordinateLinearEquivFintype

noncomputable def finiteBasisFintype {e : ℕ} (W : subspacesOfFinrank k V e) :
    Fintype (Basis (Fin e) k W.val) :=
  Fintype.ofEquiv (W.val ≃ₗ[k] Fin e → k) basisEquivCoordinateEquiv.symm

attribute [local instance] finiteBasisFintype

/-- All coordinate-equivalence torsors of the same finite dimension have the
cardinality of the corresponding general linear group. -/
noncomputable def coordinateEquivSelfEquiv (e : ℕ) (W : Type*)
    [AddCommGroup W] [Module k W] (b : Basis (Fin e) k W) :
    (W ≃ₗ[k] Fin e → k) ≃ ((Fin e → k) ≃ₗ[k] (Fin e → k)) := by
  exact {
    toFun := fun f => b.equivFun.symm.trans f
    invFun := fun g => b.equivFun.trans g
    left_inv := fun f => by
      apply LinearEquiv.ext
      intro x
      change f (b.equivFun.symm (b.equivFun x)) = f x
      rw [b.equivFun.symm_apply_apply]
    right_inv := fun g => by
      apply LinearEquiv.ext
      intro x
      change g (b.equivFun (b.equivFun.symm x)) = g x
      rw [b.equivFun.apply_symm_apply] }

/-- Every `e`-dimensional subspace has the standard number of ordered bases. -/
theorem basis_card_of_finrank_eq (e : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = e) :
    Nat.card (Basis (Fin e) k W) =
      ∏ i : Fin e, (Fintype.card k ^ e - Fintype.card k ^ (i : ℕ)) := by
  let b : Basis (Fin e) k W := (Module.finBasis k W).reindex (finCongr hW)
  calc
    Nat.card (Basis (Fin e) k W) = Nat.card (W ≃ₗ[k] Fin e → k) :=
      Nat.card_congr basisEquivCoordinateEquiv
    _ = Nat.card ((Fin e → k) ≃ₗ[k] (Fin e → k)) :=
      Nat.card_congr (coordinateEquivSelfEquiv e W b)
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin e) k) := by
      exact (Nat.card_congr
        ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun k (Fin e))).toEquiv.trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin e → k)).toEquiv)).symm
    _ = _ := by rw [Matrix.card_GL_field]

/-- The actual fixed-dimensional subspaces have the integral Gaussian count. -/
theorem subspacesOfFinrank_card_eq_gaussianBinomial (e : ℕ)
    (he : e ≤ Module.finrank k V) :
    Nat.card (subspacesOfFinrank k V e) =
      gaussianBinomial (Fintype.card k) (Module.finrank k V) e := by
  let D := ∏ i : Fin e,
    (Fintype.card k ^ e - Fintype.card k ^ (i : ℕ))
  have htotal :
      (∏ i : Fin e, (Fintype.card k ^ Module.finrank k V -
        Fintype.card k ^ (i : ℕ))) = Nat.card (subspacesOfFinrank k V e) * D := by
    calc
      _ = Nat.card {v : Fin e → V // LinearIndependent k v} :=
        (card_linearIndependent he).symm
      _ = Nat.card (Σ W : subspacesOfFinrank k V e, Basis (Fin e) k W.val) :=
        Nat.card_congr (independentFramesEquivSubspaceBasis e)
      _ = ∑ W : subspacesOfFinrank k V e, Nat.card (Basis (Fin e) k W.val) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro W hW
        rw [Nat.card_eq_fintype_card]
      _ = ∑ _W : subspacesOfFinrank k V e, D := by
        apply Finset.sum_congr rfl
        intro W hW
        unfold subspacesOfFinrank at W
        exact basis_card_of_finrank_eq e W.val W.property
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    have hq : 1 < Fintype.card k := Fintype.one_lt_card
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq i.isLt)
  rw [gaussianBinomial, ite_eq_left he]
  rw [← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  change Nat.card (subspacesOfFinrank k V e) =
    (∏ i : Fin e, (Fintype.card k ^ Module.finrank k V -
      Fintype.card k ^ (i : ℕ))) / D
  rw [htotal]
  exact (Nat.mul_div_cancel _ hD).symm

end BinaryFieldCounterexamples
