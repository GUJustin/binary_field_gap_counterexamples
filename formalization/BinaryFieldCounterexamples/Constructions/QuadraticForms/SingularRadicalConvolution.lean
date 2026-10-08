/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.QuotientComplementCount
public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularUniformity
import Mathlib.Tactic.Ring
/-!
# Actual radical convolution for totally singular subspaces

A singular subspace is decomposed into its intersection with the quadratic
radical, its actual quotient image, and a lift with those prescribed data.
The proved lift-fiber cardinality and finite-field Gaussian count give the
convolution over 0 ≤ a ≤ min(dim radical, e), with all dimensions explicit.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open scoped BigOperators
/-- The quotient image and kernel intersection partition the actual subspace dimension. -/
theorem quotient_image_inf_finrank [FiniteDimensional k V] (R S : Submodule k V) :
    Module.finrank k (S.map R.mkQ)+Module.finrank k ↥(R ⊓ S)=Module.finrank k S := by
  have h := quotientComap_finrank_add R (S.map R.mkQ)
  rw [Submodule.comap_map_mkQ] at h
  have hi := Submodule.finrank_sup_add_finrank_inf_eq R S
  omega
/-- The finite data indexing singular lifts: a radical intersection and a singular quotient image. -/
def RadicalLiftIndices (Q : QuadraticForm k V) (e : ℕ) :=
  Σ a : Fin (min (Module.finrank k Q.radical) e+1),
    subspacesOfFinrank k Q.radical a.val × TotallySingularSubspaces (Q.lift Q.radical le_rfl) (e-a.val)
/-- The actual lift fiber over the prescribed radical intersection and quotient image. -/
def RadicalLiftFiber (Q : QuadraticForm k V) (e : ℕ) (w : RadicalLiftIndices Q e) :=
  {S : Submodule k V // Q.radical ⊓ S=w.2.1.val.map Q.radical.subtype ∧
    S.map Q.radical.mkQ=w.2.2.val}
/-- Each actual lift is singular and has the prescribed total dimension. -/
noncomputable def radicalLiftToSingular [FiniteDimensional k V] (Q : QuadraticForm k V) (e : ℕ)
    (w : RadicalLiftIndices Q e) (S : RadicalLiftFiber Q e w) : TotallySingularSubspaces Q e := by
  refine ⟨S.val,?_,?_⟩
  · have h := quotient_image_inf_finrank Q.radical S.val
    rw [S.property.1,S.property.2,Submodule.finrank_map_subtype_eq,w.2.1.property,w.2.2.property.1] at h
    have he := w.1.isLt
    omega
  · apply (isotropic_map_quotient_iff Q Q.radical S.val le_rfl).mp
    rw [S.property.2]
    exact w.2.2.property.2
/-- Actual singular subspaces decompose into their radical intersection, quotient image, and lift. -/
noncomputable def radicalLiftEquiv [FiniteDimensional k V] (Q : QuadraticForm k V) (e : ℕ) :
    (Σ w : RadicalLiftIndices Q e,RadicalLiftFiber Q e w) ≃ TotallySingularSubspaces Q e := by
  apply Equiv.ofBijective (fun z => radicalLiftToSingular Q e z.1 z.2)
  constructor
  · rintro ⟨⟨a,A,T⟩,S⟩ ⟨⟨b,B,U⟩,S'⟩ heq
    have hS : S.val=S'.val := congrArg Subtype.val heq
    have hAB : A.val.map Q.radical.subtype=B.val.map Q.radical.subtype := by
      rw [←S.property.1,←S'.property.1,hS]
    have hab : a=b := by
      apply Fin.ext
      have h := congrArg (fun P : Submodule k V => Module.finrank k P) hAB
      rw [Submodule.finrank_map_subtype_eq,Submodule.finrank_map_subtype_eq,A.property,B.property] at h
      exact h
    subst b
    have hAB' : A=B := Subtype.ext (Submodule.map_injective_of_injective Q.radical.subtype_injective hAB)
    subst B
    have hTU : T=U := by
      apply Subtype.ext
      rw [←S.property.2,←S'.property.2,hS]
    subst U
    have hSS : S=S' := Subtype.ext hS
    subst S'
    rfl
  · intro S
    let A := (Q.radical ⊓ S.val).comap Q.radical.subtype
    have hA : A.map Q.radical.subtype=Q.radical ⊓ S.val := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr inf_le_left
    have hdimA : Module.finrank k A=Module.finrank k ↥(Q.radical ⊓ S.val) := by
      rw [←hA,Submodule.finrank_map_subtype_eq]
    have hleR : Module.finrank k A≤Module.finrank k Q.radical := Submodule.finrank_le _
    have hleS : Module.finrank k A≤e := by
      rw [hdimA]
      exact (Submodule.finrank_mono inf_le_right).trans_eq S.property.1
    let a : Fin (min (Module.finrank k Q.radical) e+1) := ⟨Module.finrank k A,by omega⟩
    let T := S.val.map Q.radical.mkQ
    have hTdim : Module.finrank k T=e-a.val := by
      have h := quotient_image_inf_finrank Q.radical S.val
      rw [←hdimA,S.property.1] at h
      change Module.finrank k T+ a.val=e at h
      omega
    have hT : ∀ z ∈ T,Q.lift Q.radical le_rfl z=0 :=
      (isotropic_map_quotient_iff Q Q.radical S.val le_rfl).mpr S.property.2
    refine ⟨⟨⟨a,⟨A,rfl⟩,⟨T,hTdim,hT⟩⟩,⟨S.val,hA.symm,rfl⟩⟩,?_⟩
    rfl
/-- The actual finite singular-subspace count is the safe radical convolution of the radical-free quotient counts. -/
theorem totallySingularSubspaces_radical_convolution [Fintype k] [Fintype V]
    (Q : QuadraticForm k V) (e : ℕ) :
    Nat.card (TotallySingularSubspaces Q e)=
      ∑ a ∈ Finset.range (min (Module.finrank k Q.radical) e+1),
        gaussianBinomial (Fintype.card k) (Module.finrank k Q.radical) a *
          (Fintype.card k)^((Module.finrank k Q.radical-a)*(e-a)) *
          Nat.card (TotallySingularSubspaces (Q.lift Q.radical le_rfl) (e-a)) := by
  classical
  let : Fintype (Submodule k V) := Fintype.ofInjective (fun L : Submodule k V => (L : Set V)) SetLike.coe_injective
  let : Fintype (Submodule k Q.radical) := Fintype.ofInjective (fun L : Submodule k Q.radical => (L : Set Q.radical)) SetLike.coe_injective
  let : Fintype (Submodule k (V ⧸ Q.radical)) := Fintype.ofInjective (fun L : Submodule k (V ⧸ Q.radical) => (L : Set (V ⧸ Q.radical))) SetLike.coe_injective
  let (a : ℕ) : Fintype (TotallySingularSubspaces (Q.lift Q.radical le_rfl) a) := by
    unfold TotallySingularSubspaces; exact Fintype.ofFinite _
  let : Fintype (RadicalLiftIndices Q e) := by unfold RadicalLiftIndices; infer_instance
  let (w : RadicalLiftIndices Q e) : Fintype (RadicalLiftFiber Q e w) := by
    unfold RadicalLiftFiber; exact Fintype.ofFinite _
  have hf (w : RadicalLiftIndices Q e) : Nat.card (RadicalLiftFiber Q e w)=
      (Fintype.card k)^((Module.finrank k Q.radical-w.1.val)*(e-w.1.val)) := by
    change Nat.card {S : Submodule k V // Q.radical ⊓ S=w.2.1.val.map Q.radical.subtype ∧
      S.map Q.radical.mkQ=w.2.2.val}=_
    rw [quotient_lift_fiber_natCard _ _ (by intro x hx; obtain ⟨y,hy,rfl⟩ := hx; exact y.property),
      Submodule.finrank_map_subtype_eq,w.2.1.property,w.2.2.property.1,Nat.mul_comm]
  rw [←Nat.card_congr (radicalLiftEquiv Q e),Nat.card_sigma]
  simp only [hf]
  change (∑ w : (Σ a : Fin (min (Module.finrank k Q.radical) e+1),
    subspacesOfFinrank k Q.radical a.val × TotallySingularSubspaces (Q.lift Q.radical le_rfl) (e-a.val)),
      (Fintype.card k)^((Module.finrank k Q.radical-w.1.val)*(e-w.1.val)))=_
  rw [Fintype.sum_sigma]
  change (∑ a : Fin (min (Module.finrank k Q.radical) e+1),
    ∑ w : subspacesOfFinrank k Q.radical a.val × TotallySingularSubspaces (Q.lift Q.radical le_rfl) (e-a.val),
      (Fintype.card k)^((Module.finrank k Q.radical-a.val)*(e-a.val)))=_
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul]
  have hg := subspacesOfFinrank_card_eq_gaussianBinomial (k:=k) (V:=Q.radical) a.val
    (by have h := a.isLt; omega)
  rw [Nat.card_eq_fintype_card] at hg
  rw [hg,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id]
  ring
end BinaryFieldCounterexamples.QuadraticGeometry
