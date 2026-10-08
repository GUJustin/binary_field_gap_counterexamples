/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.JointSurjectiveCount
/-!
# Root-coordinate decomposition of binary tree frames

A nonzero binary root functional splits a frame into two restricted child maps
and their values on a root direction. Surjectivity of the frame is exactly joint
surjectivity of the two restricted child maps.
-/
@[expose] public section

namespace BinaryFieldCounterexamples.Trees
set_option maxHeartbeats 800000

variable {V T : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup T] [Module (ZMod 2) T] [Finite V] [Finite T]

/-- First coordinate of a frame. -/
def rootFirst (L : V →ₗ[ZMod 2] (ZMod 2 × T × T)) : V →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.fst (ZMod 2) (ZMod 2) (T×T)).comp L

/-- Left child coordinate of a frame. -/
def rootLeft (L : V →ₗ[ZMod 2] (ZMod 2 × T × T)) : V →ₗ[ZMod 2] T :=
  (LinearMap.fst (ZMod 2) T T).comp
    ((LinearMap.snd (ZMod 2) (ZMod 2) (T×T)).comp L)

/-- Right child coordinate of a frame. -/
def rootRight (L : V →ₗ[ZMod 2] (ZMod 2 × T × T)) : V →ₗ[ZMod 2] T :=
  (LinearMap.snd (ZMod 2) T T).comp
    ((LinearMap.snd (ZMod 2) (ZMod 2) (T×T)).comp L)

/-- Left child map restricted to the kernel of the root functional. -/
def rootRestrictedLeft (z : V →ₗ[ZMod 2] ZMod 2)
    (L : V →ₗ[ZMod 2] (ZMod 2 × T × T)) : LinearMap.ker z →ₗ[ZMod 2] T :=
  (rootLeft L).domRestrict (LinearMap.ker z)

/-- Right child map restricted to the kernel of the root functional. -/
def rootRestrictedRight (z : V →ₗ[ZMod 2] ZMod 2)
    (L : V →ₗ[ZMod 2] (ZMod 2 × T × T)) : LinearMap.ker z →ₗ[ZMod 2] T :=
  (rootRight L).domRestrict (LinearMap.ker z)

/-- A binary linear map out of the scalar field is determined by its value at one. -/
noncomputable def binaryLinearMapEquiv : (ZMod 2 →ₗ[ZMod 2] T) ≃ T := {
  toFun := fun f => f 1
  invFun := LinearMap.toSpanSingleton (ZMod 2) T
  left_inv := by
    intro f
    apply LinearMap.ext
    intro c
    change c • f 1=f c
    simpa only [smul_eq_mul, mul_one] using (f.map_smul c 1).symm
  right_inv := by intro x; simp [LinearMap.toSpanSingleton_apply] }

/-- A frame with fixed first coordinate is equivalent to its two child maps. -/
noncomputable def fixedFirstEquiv (z : V →ₗ[ZMod 2] ZMod 2) :
    {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z} ≃
      ((V →ₗ[ZMod 2] T) × (V →ₗ[ZMod 2] T)) := {
  toFun := fun L => (rootLeft L,rootRight L)
  invFun := fun p => ⟨z.prod (p.1.prod p.2),by ext x; rfl⟩
  left_inv := by
    intro L
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change z x=(L.1 x).1
      exact (LinearMap.congr_fun L.2 x).symm
    · rfl
  right_inv := by intro p; rfl }

/-- Root coordinates identify a fixed-root frame with two restricted maps and two root values. -/
noncomputable def rootFrameComponentsEquiv (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z) :
    {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z} ≃
      (((LinearMap.ker z →ₗ[ZMod 2] T) × T) ×
        ((LinearMap.ker z →ₗ[ZMod 2] T) × T)) := by
  let E : (V →ₗ[ZMod 2] T) ≃
      ((LinearMap.ker z →ₗ[ZMod 2] T) × (ZMod 2 →ₗ[ZMod 2] T)) :=
    ((splitAtSurjection z hz).arrowCongr (LinearEquiv.refl (ZMod 2) T)).toEquiv.trans
      (LinearMap.coprodEquiv (ZMod 2)).symm.toEquiv
  let C := E.trans ((Equiv.refl _).prodCongr binaryLinearMapEquiv)
  exact (fixedFirstEquiv z).trans (C.prodCongr C)


/-- The first restricted component is the left restriction. -/
theorem rootFrameComponents_left (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z)
    (L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z}) :
    (rootFrameComponentsEquiv z hz L).1.1=rootRestrictedLeft z L := by
  ext k
  simp [rootFrameComponentsEquiv,rootRestrictedLeft,fixedFirstEquiv,rootLeft,
    splitAtSurjection]

/-- The second restricted component is the right restriction. -/
theorem rootFrameComponents_right (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z)
    (L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z}) :
    (rootFrameComponentsEquiv z hz L).2.1=rootRestrictedRight z L := by
  ext k
  simp [rootFrameComponentsEquiv,rootRestrictedRight,fixedFirstEquiv,rootRight,
    splitAtSurjection]


/-- Evaluation formula for the left child map in root coordinates. -/
theorem rootFrameComponents_left_apply (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z)
    (L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z})
    (k : LinearMap.ker z) (c : ZMod 2) :
    rootLeft L ((splitAtSurjection z hz).symm (k,c))=
      (rootFrameComponentsEquiv z hz L).1.1 k+c •
        (rootFrameComponentsEquiv z hz L).1.2 := by
  simp [rootFrameComponentsEquiv,fixedFirstEquiv,binaryLinearMapEquiv,rootLeft]
  have hp : (k,c)=(k,0)+c • (0,1) := by ext <;> simp
  rw [hp,map_add,map_smul,map_add,map_smul]
  rfl

/-- Evaluation formula for the right child map in root coordinates. -/
theorem rootFrameComponents_right_apply (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z)
    (L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z})
    (k : LinearMap.ker z) (c : ZMod 2) :
    rootRight L ((splitAtSurjection z hz).symm (k,c))=
      (rootFrameComponentsEquiv z hz L).2.1 k+c •
        (rootFrameComponentsEquiv z hz L).2.2 := by
  simp [rootFrameComponentsEquiv,fixedFirstEquiv,binaryLinearMapEquiv,rootRight]
  have hp : (k,c)=(k,0)+c • (0,1) := by ext <;> simp
  rw [hp,map_add,map_smul,map_add,map_smul]
  rfl


/-- A fixed-root frame is onto exactly when its two kernel restrictions are jointly onto. -/
theorem rootFrame_surjective_iff (z : V →ₗ[ZMod 2] ZMod 2)
    (hz : Function.Surjective z)
    (L : {L : V →ₗ[ZMod 2] (ZMod 2 × T × T) // rootFirst L=z}) :
    Function.Surjective L.1 ↔ Function.Surjective
      ((rootFrameComponentsEquiv z hz L).1.1.prod
        (rootFrameComponentsEquiv z hz L).2.1) := by
  let C := rootFrameComponentsEquiv z hz L
  let e := splitAtSurjection z hz
  have he (k : LinearMap.ker z) (c : ZMod 2) : z (e.symm (k,c))=c := by
    change z (k+(Classical.choose (z.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hz))) c)=c
    rw [map_add,show z k=0 from k.2,zero_add]
    have hs := LinearMap.congr_fun (Classical.choose_spec
      (z.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hz))) c
    simpa only [LinearMap.comp_apply,LinearMap.id_coe,id_eq] using hs
  constructor
  · intro hsurj p
    obtain ⟨x,hx⟩ := hsurj (0,p.1,p.2)
    have hzx : z x=0 := by
      have hf := LinearMap.congr_fun L.2 x
      change (L.1 x).1=z x at hf
      exact hf.symm.trans (congrArg Prod.fst hx)
    let k : LinearMap.ker z := ⟨x,hzx⟩
    refine ⟨k,?_⟩
    apply Prod.ext
    · change C.1.1 k=p.1
      rw [show C.1.1=rootRestrictedLeft z L from rootFrameComponents_left z hz L]
      exact congrArg (fun y => y.2.1) hx
    · change C.2.1 k=p.2
      rw [show C.2.1=rootRestrictedRight z L from rootFrameComponents_right z hz L]
      exact congrArg (fun y => y.2.2) hx
  · intro hsurj p
    obtain ⟨k,hk⟩ := hsurj
      (p.2.1-p.1 • C.1.2,p.2.2-p.1 • C.2.2)
    refine ⟨e.symm (k,p.1),?_⟩
    apply Prod.ext
    · have hf := LinearMap.congr_fun L.2 (e.symm (k,p.1))
      change (L.1 (e.symm (k,p.1))).1=z (e.symm (k,p.1)) at hf
      exact hf.trans (he k p.1)
    · apply Prod.ext
      · change rootLeft L (e.symm (k,p.1))=p.2.1
        rw [rootFrameComponents_left_apply z hz L]
        change C.1.1 k+p.1 • C.1.2=p.2.1
        have hu := congrArg Prod.fst hk
        dsimp only [LinearMap.prod_apply] at hu
        change C.1.1 k=p.2.1-p.1 • C.1.2 at hu
        rw [hu]
        abel
      · change rootRight L (e.symm (k,p.1))=p.2.2
        rw [rootFrameComponents_right_apply z hz L]
        change C.2.1 k+p.1 • C.2.2=p.2.2
        have hv := congrArg Prod.snd hk
        dsimp only [LinearMap.prod_apply] at hv
        change C.2.1 k=p.2.2-p.1 • C.2.2 at hv
        rw [hv]
        abel



end BinaryFieldCounterexamples.Trees
