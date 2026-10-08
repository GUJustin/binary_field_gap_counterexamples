/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectiveLinearCount
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Jointly surjective binary linear maps

For a fixed surjection `A`, joint surjectivity of `(A,B)` is equivalent to
surjectivity of the restriction of `B` to `ker A`. Splitting along a linear
section gives the exact population.
-/
@[expose] public section

namespace BinaryFieldCounterexamples.Trees

variable {H T : Type*} [AddCommGroup H] [Module (ZMod 2) H]
  [AddCommGroup T] [Module (ZMod 2) T] [Finite H] [Finite T]

/-- A surjection splits its source into its kernel and target. -/
noncomputable def splitAtSurjection (A : H →ₗ[ZMod 2] T) (hA : Function.Surjective A) :
    H ≃ₗ[ZMod 2] LinearMap.ker A × T := by
  let S : T →ₗ[ZMod 2] H := Classical.choose
    (A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA))
  have hS : A.comp S = LinearMap.id := Classical.choose_spec
    (A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA))
  let π : H →ₗ[ZMod 2] LinearMap.ker A := {
    toFun := fun x => ⟨x-S (A x),by
      change A (x-S (A x))=0
      rw [map_sub]
      have he := LinearMap.congr_fun hS (A x)
      simpa only [LinearMap.comp_apply,LinearMap.id_coe,id_eq] using sub_eq_zero.mpr he.symm⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change (x+y)-S (A (x+y))=(x-S (A x))+(y-S (A y))
      simp only [map_add]
      abel
    map_smul' := by
      intro c x
      apply Subtype.ext
      change c • x-S (A (c • x))=c • (x-S (A x))
      simp only [map_smul,smul_sub] }
  exact {
    toFun := fun x => (π x,A x)
    invFun := fun p => p.1+S p.2
    left_inv := by
      intro x
      dsimp only
      change (x-S (A x))+S (A x)=x
      abel
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        change (p.1+S p.2)-S (A (p.1+S p.2))=p.1
        rw [map_add,show A p.1=0 from p.1.2,zero_add]
        have he := LinearMap.congr_fun hS p.2
        simp only [LinearMap.comp_apply,LinearMap.id_coe,id_eq] at he
        rw [he]
        abel
      · dsimp only
        rw [map_add,show A p.1=0 from p.1.2]
        have he := LinearMap.congr_fun hS p.2
        simpa only [LinearMap.comp_apply,LinearMap.id_coe,id_eq,zero_add] using he
    map_add' := by
      intro x y
      apply Prod.ext
      · exact congrArg Subtype.val (map_add π x y) |> Subtype.ext
      · exact map_add A x y
    map_smul' := by
      intro c x
      apply Prod.ext
      · exact congrArg Subtype.val (map_smul π c x) |> Subtype.ext
      · exact map_smul A c x }

/-- Maps out of the source are the restriction to the kernel plus arbitrary
values on a chosen section. -/
noncomputable def linearMapsAtSurjectionEquiv (A : H →ₗ[ZMod 2] T)
    (hA : Function.Surjective A) :
    (H →ₗ[ZMod 2] T) ≃ ((LinearMap.ker A →ₗ[ZMod 2] T) × (T →ₗ[ZMod 2] T)) :=
  ((splitAtSurjection A hA).arrowCongr (LinearEquiv.refl (ZMod 2) T)).toEquiv.trans
    (LinearMap.coprodEquiv (ZMod 2)).symm.toEquiv

/-- The pair `(A,B)` is onto exactly when `B` is onto on `ker A`. -/
theorem jointSurjective_iff (A : H →ₗ[ZMod 2] T)
    (hA : Function.Surjective A) (B : H →ₗ[ZMod 2] T) :
    Function.Surjective (A.prod B) ↔
      Function.Surjective (linearMapsAtSurjectionEquiv A hA B).1 := by
  let e := splitAtSurjection A hA
  let C := linearMapsAtSurjectionEquiv A hA B
  have heA (p : LinearMap.ker A × T) : A (e.symm p)=p.2 := by
    change A (p.1+(Classical.choose (A.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hA))) p.2)=p.2
    rw [map_add,show A p.1=0 from p.1.2,zero_add]
    have hS := LinearMap.congr_fun (Classical.choose_spec
      (A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA))) p.2
    simpa only [LinearMap.comp_apply,LinearMap.id_coe,id_eq] using hS
  have hC (p : LinearMap.ker A × T) : B (e.symm p)=C.1 p.1+C.2 p.2 := by
    dsimp [C,linearMapsAtSurjectionEquiv]
    simp only [LinearEquiv.trans_apply,LinearEquiv.arrowCongr_apply,
      LinearEquiv.refl_symm,LinearEquiv.refl_apply,LinearMap.coprodEquiv_symm_apply,
      LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,LinearMap.map_add]
    rw [←map_add]
    congr 1
    rw [←e.symm.map_add]
    congr 1 <;> simp
  constructor
  · intro hs u
    obtain ⟨x,hx⟩ := hs (0,u)
    refine ⟨⟨x,?_⟩,?_⟩
    · exact congrArg Prod.fst hx
    · have hc := hC (e x)
      rw [e.symm_apply_apply] at hc
      have he1 : (e x).1=⟨x,by exact congrArg Prod.fst hx⟩ := by
        apply Subtype.ext
        change x-(Classical.choose (A.exists_rightInverse_of_surjective
          (LinearMap.range_eq_top.mpr hA))) (A x)=x
        rw [show A x=0 from congrArg Prod.fst hx]
        simp
      rw [he1,show (e x).2=0 from congrArg Prod.fst hx,map_zero,add_zero] at hc
      exact hc.symm.trans (congrArg Prod.snd hx)
  · intro hs p
    obtain ⟨k,hk⟩ := hs (p.2-C.2 p.1)
    refine ⟨e.symm (k,p.1),?_⟩
    apply Prod.ext
    · exact heA (k,p.1)
    · change B (e.symm (k,p.1))=p.2
      rw [hC,hk]
      abel

/-- Jointly surjective maps correspond to a surjection from the kernel and an
arbitrary endomorphism of the target. -/
noncomputable def jointSurjectiveEquiv (A : H →ₗ[ZMod 2] T)
    (hA : Function.Surjective A) :
    {B : H →ₗ[ZMod 2] T // Function.Surjective (A.prod B)} ≃
      ({C : LinearMap.ker A →ₗ[ZMod 2] T // Function.Surjective C} ×
        (T →ₗ[ZMod 2] T)) := {
  toFun := fun B =>
    (⟨(linearMapsAtSurjectionEquiv A hA B).1,
      (by
        rw [← jointSurjective_iff A hA B]
        exact B.2)⟩,
      (linearMapsAtSurjectionEquiv A hA B).2)
  invFun := fun p =>
    ⟨(linearMapsAtSurjectionEquiv A hA).symm (p.1,p.2),
      (jointSurjective_iff A hA _).mpr (by
        simpa only [Equiv.apply_symm_apply] using p.1.2)⟩
  left_inv := by
    intro B
    apply Subtype.ext
    exact (linearMapsAtSurjectionEquiv A hA).symm_apply_apply B
  right_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((linearMapsAtSurjectionEquiv A hA).apply_symm_apply (p.1,p.2))
    · change ((linearMapsAtSurjectionEquiv A hA)
          ((linearMapsAtSurjectionEquiv A hA).symm (p.1,p.2))).2=p.2
      exact congrArg Prod.snd
        ((linearMapsAtSurjectionEquiv A hA).apply_symm_apply (p.1,p.2)) }

/-- Exact cardinality of the binary endomorphism space. -/
theorem linearEnd_card : Nat.card (T →ₗ[ZMod 2] T) =
    2^(Module.finrank (ZMod 2) T)^2 := by
  classical
  let : Finite (Module.Dual (ZMod 2) T) := Finite.of_injective
    (fun f : Module.Dual (ZMod 2) T => (f : T → ZMod 2)) DFunLike.coe_injective
  let e := Module.finBasis (ZMod 2) T
  rw [Nat.card_congr (linearMapDualFrameEquiv (V := T) e)]
  rw [Nat.card_fun]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Module.Dual (ZMod 2) T)
  simp only [Nat.card_eq_fintype_card,ZMod.card,Subspace.dual_finrank_eq] at hc
  rw [hc,Nat.card_fin,←pow_mul,pow_two]

/-- Exact count of maps jointly surjective with a fixed binary surjection. -/
theorem jointSurjectiveLinearMaps_card (A : H →ₗ[ZMod 2] T)
    (hA : Function.Surjective A)
    (hdim : 2*Module.finrank (ZMod 2) T ≤ Module.finrank (ZMod 2) H) :
    Nat.card {B : H →ₗ[ZMod 2] T // Function.Surjective (A.prod B)} =
      2^(Module.finrank (ZMod 2) T)^2 *
        ∏ i : Fin (Module.finrank (ZMod 2) T),
          (2^(Module.finrank (ZMod 2) H-Module.finrank (ZMod 2) T)-2^(i:ℕ)) := by
  classical
  have hrange : Module.finrank (ZMod 2) (LinearMap.range A)=
      Module.finrank (ZMod 2) T := by
    rw [LinearMap.range_eq_top.mpr hA]
    exact finrank_top (ZMod 2) T
  have hrank := LinearMap.finrank_range_add_finrank_ker A
  rw [hrange] at hrank
  have hker : Module.finrank (ZMod 2) (LinearMap.ker A)=
      Module.finrank (ZMod 2) H-Module.finrank (ZMod 2) T := by omega
  have hle : Module.finrank (ZMod 2) T ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) := by omega
  rw [Nat.card_congr (jointSurjectiveEquiv A hA),Nat.card_prod,
    surjectiveLinearMaps_card hle,linearEnd_card,hker]
  exact Nat.mul_comm _ _

end BinaryFieldCounterexamples.Trees
