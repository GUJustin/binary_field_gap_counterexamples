/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.SubspaceIncidence
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Prod
/-!
# An explicit population of codimension-s subspaces

Graphs of binary linear maps from an m-dimensional space to an s-dimensional
space give exactly 2^(m*s) distinct subspaces of size 2^m. Transport through a
linear equivalence realizes this population inside every prescribed space of
dimension m+s. For the all-rate theorem, this subfamily already has the required
N^s growth; the fixed factor 2^(s*s) is absorbed into its unspecified constant.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

theorem linearMap_graph_injective {U S : Type*} [AddCommGroup U] [AddCommGroup S]
    [Module (ZMod 2) U] [Module (ZMod 2) S] :
    Function.Injective (fun A : U →ₗ[ZMod 2] S => A.graph) := by
  intro A B he
  change A.graph=B.graph at he
  ext x
  have hx : (x,A x)∈A.graph := rfl
  rw [he] at hx
  exact hx

theorem natCard_linearMap_graph {U S : Type*} [AddCommGroup U] [AddCommGroup S]
    [Module (ZMod 2) U] [Module (ZMod 2) S] (A : U →ₗ[ZMod 2] S) :
    Nat.card A.graph=Nat.card U := by
  apply Nat.card_congr
  exact { toFun := fun x => x.val.1
          invFun := fun x => ⟨(x,A x),rfl⟩
          left_inv := fun x => by apply Subtype.ext; exact Prod.ext rfl x.property.symm
          right_inv := fun x => rfl }

theorem exists_binary_graph_subspace_family
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (m s : ℕ) (hd : Module.finrank (ZMod 2) V=m+s) :
    ∃ I : Finset (Submodule (ZMod 2) V), I.card=2^(m*s) ∧
      ∀ W∈I, Nat.card W=2^m := by
  let U := Fin m → ZMod 2
  let S := Fin s → ZMod 2
  let e : (U×S) ≃ₗ[ZMod 2] V := LinearEquiv.ofFinrankEq (R := ZMod 2) (U×S) V (by
    simp only [Module.finrank_prod,Module.finrank_pi,
      Fintype.card_fin,hd,U,S])
  let : Fintype (U →ₗ[ZMod 2] S) := Fintype.ofInjective (fun A : U →ₗ[ZMod 2] S => (A : U → S)) DFunLike.coe_injective
  let E := (Submodule.orderIsoMapComap e).toEquiv
  let I : Finset (Submodule (ZMod 2) V) := Finset.univ.image (fun A : U →ₗ[ZMod 2] S => E A.graph)
  have hinj : Function.Injective (fun A : U →ₗ[ZMod 2] S => E A.graph) :=
    fun A B he => linearMap_graph_injective (E.injective he)
  refine ⟨I,?_,?_⟩
  · dsimp only [I]
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U →ₗ[ZMod 2] S)
    simpa [Nat.card_eq_fintype_card,Module.finrank_linearMap,Module.finrank_pi,U,S] using hc
  · intro W hW
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    have hc : Nat.card (E A.graph)=Nat.card A.graph :=
      (Nat.card_congr (e.submoduleMap A.graph).toEquiv).symm
    rw [hc,natCard_linearMap_graph]
    simp [U,Nat.card_eq_fintype_card]
/-- The graph population lies in the prescribed field subgroup itself. -/
theorem exists_binary_graph_subgroup_family
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (m s : ℕ) (hD : Nat.card D=2^(m+s)) :
    ∃ I : Finset (AddSubgroup F), I.card=2^(m*s) ∧
      ∀ W∈I, W≤D ∧ Nat.card W=2^m := by
  have hdim : Module.finrank (ZMod 2) D=m+s := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD] at he
    simp only [Nat.card_eq_fintype_card,ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2≤2) he.symm
  obtain ⟨I,hI,hsize⟩ := exists_binary_graph_subspace_family D m s hdim
  let e : Submodule (ZMod 2) D → AddSubgroup F := fun W => W.toAddSubgroup.map D.subtype
  have hi : Function.Injective e := by
    intro W U he
    apply Submodule.toAddSubgroup_injective
    ext x
    have hx : ((x:F)∈e W) ↔ ((x:F)∈e U) := by rw [he]
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := hx.mp ⟨x,h,rfl⟩
      have hyx : y=x := Subtype.val_injective he
      exact hyx ▸ hy
    · intro h
      obtain ⟨y,hy,he⟩ := hx.mpr ⟨x,h,rfl⟩
      have hyx : y=x := Subtype.val_injective he
      exact hyx ▸ hy
  refine ⟨I.image e,by rw [Finset.card_image_of_injective _ hi,hI],?_⟩
  intro W hW
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hW
  refine ⟨?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact y.property
  · have hc : Nat.card (e U)=Nat.card U := AddSubgroup.card_map_of_injective Subtype.val_injective
    rw [hc,hsize U hU]
end BinaryFieldCounterexamples
