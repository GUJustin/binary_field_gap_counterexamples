/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Definition
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.HeightTwo
public import BinaryFieldCounterexamples.Constructions.Trees.Leaves
/-!
# Intrinsic trees and affine template coordinates

The recursive data of Definition 6.3 in Section 6.2 of the paper are
equivalent to surjective affine coordinates for the existing templates.
Disjoint essential dual spaces make the two child coordinate maps jointly
surjective. Splitting at the root then gives the template coordinates.
The recursive bridge uses the proved degree-free characterization of the
height-two predicate; its definition itself includes Boolean degree.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
set_option backward.isDefEq.respectTransparency false
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype

variable {U T : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup T] [Module (ZMod 2) T]

/-- Two onto coordinate maps are jointly onto exactly when their essential
coordinate spaces (the annihilators of their kernels) intersect trivially. -/
theorem jointSurjective_iff_disjoint_dualAnnihilator
    (A B : U →ₗ[ZMod 2] T) (hA : Function.Surjective A)
    (hB : Function.Surjective B) :
    Function.Surjective (A.prod B) ↔ A.ker.dualAnnihilator ⊓ B.ker.dualAnnihilator = ⊥ := by
  have he : Function.Surjective (A.prod B) ↔ A.ker ⊔ B.ker = ⊤ := by
    constructor
    · intro h
      apply Submodule.eq_top_iff'.mpr
      intro x
      obtain ⟨y, hy⟩ := h (A x, 0)
      have hAy : A y = A x := congrArg Prod.fst hy
      have hBy : B y = 0 := congrArg Prod.snd hy
      apply Submodule.mem_sup.mpr
      refine ⟨x-y, ?_, y, hBy, by abel⟩
      change A (x-y) = 0
      simp only [map_sub, hAy, sub_self]
    · intro h
      apply LinearMap.range_eq_top.mp
      rw [LinearMap.range_prod_eq h, LinearMap.range_eq_top.mpr hA,
        LinearMap.range_eq_top.mpr hB]
      ext x
      simp
  rw [he, ← Subspace.dualAnnihilator_inj,
    Submodule.dualAnnihilator_sup_eq, Submodule.dualAnnihilator_top]

/-- Projection onto the root kernel along the chosen point in the one-slice. -/
def treeRootProjection (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p = 1) :
    U →ₗ[ZMod 2] s.ker := {
  toFun := fun x => ⟨x - s x • p, by simp [map_sub, map_smul, hp]⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [map_add, add_smul, Submodule.coe_add]
    abel
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [map_smul, smul_sub, smul_smul, Submodule.coe_smul,
      smul_eq_mul, RingHom.id_apply, mul_comm c] }

@[simp] theorem treeRootProjection_apply_ker (s : Module.Dual (ZMod 2) U)
    (p : U) (hp : s p = 1) (x : s.ker) : treeRootProjection s p hp x = x := by
  apply Subtype.ext
  simp [treeRootProjection, show s x = 0 from x.property]

@[simp] theorem treeRootProjection_apply_add (s : Module.Dual (ZMod 2) U)
    (p : U) (hp : s p = 1) (x : s.ker) (c : ZMod 2) :
    treeRootProjection s p hp (c • p + x) = x := by
  apply Subtype.ext
  simp [treeRootProjection, hp, show s x = 0 from x.property]

/-- Affine child coordinates combine with a root test into template coordinates. -/
def treeRootAffineMap (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p = 1)
    (a b : s.ker →ᵃ[ZMod 2] T) : U →ᵃ[ZMod 2] (ZMod 2 × T × T) :=
  s.toAffineMap.prod ((a.comp (treeRootProjection s p hp).toAffineMap).prod
    (b.comp (treeRootProjection s p hp).toAffineMap))

/-- Joint surjectivity of child linear maps gives surjectivity of the entire tree map. -/
theorem treeRootAffineMap_surjective (s : Module.Dual (ZMod 2) U)
    (p : U) (hp : s p = 1) (a b : s.ker →ᵃ[ZMod 2] T)
    (hab : Function.Surjective (a.linear.prod b.linear)) :
    Function.Surjective (treeRootAffineMap s p hp a b) := by
  have hab' : Function.Surjective (a.prod b) :=
    (a.prod b).linear_surjective_iff.mp hab
  rintro ⟨c, u, v⟩
  obtain ⟨x, hx⟩ := hab' (u,v)
  refine ⟨c • p + x, ?_⟩
  apply Prod.ext
  · simp [treeRootAffineMap, hp, show s x = 0 from x.property]
  · simpa [treeRootAffineMap] using hx

/-- Reversing the root bit while interchanging the children computes the same
branch function. This normalizes an affine root coordinate to have zero offset. -/
def treeRootSwapAffine : (ZMod 2 × T × T) →ᵃ[ZMod 2] (ZMod 2 × T × T) :=
  ((LinearMap.fst (ZMod 2) (ZMod 2) (T × T)).toAffineMap +
    AffineMap.const (ZMod 2) _ 1).prod
      (((LinearMap.snd (ZMod 2) T T).comp
        (LinearMap.snd (ZMod 2) (ZMod 2) (T × T))).toAffineMap.prod
      ((LinearMap.fst (ZMod 2) T T).comp
        (LinearMap.snd (ZMod 2) (ZMod 2) (T × T))).toAffineMap)

@[simp] theorem treeRootSwapAffine_apply (x : ZMod 2 × T × T) :
    treeRootSwapAffine x = (x.1 + 1, x.2.2, x.2.1) := by rfl

theorem treeRootSwapAffine_surjective : Function.Surjective
    (treeRootSwapAffine : (ZMod 2 × T × T) →ᵃ[ZMod 2] _) := by
  rintro ⟨c,u,v⟩
  refine ⟨(c+1,v,u), ?_⟩
  simp [add_assoc, show (1:ZMod 2)+1=0 by decide]

theorem branch_treeRootSwapAffine (f : T → ZMod 2) (x : ZMod 2 × T × T) :
    branch f f (treeRootSwapAffine x) = branch f f x := by
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) x.1 with hc | hc <;>
    simp [branch, hc, show (1:ZMod 2)+1=0 by decide]

/-- Every affine pullback representation can be chosen with zero root offset. -/
theorem exists_root_normalized_pullback (n : ℕ)
    (a : U →ᵃ[ZMod 2] TemplateSpace (n+1)) (ha : Function.Surjective a) :
    ∃ b : U →ᵃ[ZMod 2] TemplateSpace (n+1),
      Function.Surjective b ∧ (b 0).1=0 ∧
      (fun x => template (n+1) (b x)) = (fun x => template (n+1) (a x)) := by
  letI := templateSpaceAddCommGroup n
  letI := templateSpaceModule n
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (a 0).1 with hc | hc
  · exact ⟨a,ha,hc,rfl⟩
  · refine ⟨(treeRootSwapAffine (T := TemplateSpace n)).comp a,
      treeRootSwapAffine_surjective.comp ha, ?_, ?_⟩
    · change (a 0).1 + 1 = 0
      rw [hc]
      decide
    · funext x
      exact branch_treeRootSwapAffine (template n) (a x)

/-- Independent affine coordinates for the intrinsic children assemble into
surjective affine coordinates for their parent. The only compatibility
condition is disjointness of the actual essential dual spaces. -/
theorem mem_affinePullbackFamily_of_intrinsic_root (n : ℕ) (φ : U → ZMod 2)
    (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p=1)
    (h₀ : (fun x : s.ker => φ x) ∈ affinePullbackFamily s.ker (template n))
    (h₁ : (fun x : s.ker => φ (p+x)) ∈ affinePullbackFamily s.ker (template n))
    (hdisj : essentialDualSpace (fun x : s.ker => φ x) ⊓
      essentialDualSpace (fun x : s.ker => φ (p+x)) = ⊥) :
    φ ∈ affinePullbackFamily U (template (n+1)) := by
  obtain ⟨⟨a,ha⟩,heqa⟩ := h₀
  obtain ⟨⟨b,hb⟩,heqb⟩ := h₁
  change (fun x => template n (a x)) = (fun x : s.ker => φ x) at heqa
  change (fun x => template n (b x)) = (fun x : s.ker => φ (p+x)) at heqb
  have hea := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) a ha
  have heb := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) b hb
  rw [heqa] at hea
  rw [heqb] at heb
  rw [hea,heb] at hdisj
  have hab := (jointSurjective_iff_disjoint_dualAnnihilator a.linear b.linear
    (a.linear_surjective_iff.mpr ha) (b.linear_surjective_iff.mpr hb)).mpr hdisj
  refine ⟨⟨treeRootAffineMap (T := TemplateSpace n) s p hp a b,
    treeRootAffineMap_surjective s p hp a b hab⟩, ?_⟩
  funext x
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (s x) with hx | hx
  · change (if s x = 0 then template n (a (treeRootProjection s p hp x))
      else template n (b (treeRootProjection s p hp x))) = φ x
    rw [hx,ite_eq_left rfl]
    exact (congrFun heqa (treeRootProjection s p hp x)).trans
      (by change φ (x-s x • p)=φ x; simp [hx])
  · change (if s x = 0 then template n (a (treeRootProjection s p hp x))
      else template n (b (treeRootProjection s p hp x))) = φ x
    rw [hx,ite_eq_right one_ne_zero]
    exact (congrFun heqb (treeRootProjection s p hp x)).trans
      (by change φ (p+(x-s x • p))=φ x; rw [hx,one_smul]; congr 1; abel)

/-- A pullback supplies literal intrinsic root data: the child essential
spaces have the prescribed dimension and trivial intersection. The child
predicates are left as pullback membership for the recursive induction. -/
theorem exists_intrinsic_root_of_affinePullbackFamily (n : ℕ) (φ : U → ZMod 2)
    (hφ : φ ∈ affinePullbackFamily U (template (n+1))) :
    ∃ s : Module.Dual (ZMod 2) U, s ≠ 0 ∧
      ∃ p : U, s p = 1 ∧
        (fun x : s.ker => φ x) ∈ affinePullbackFamily s.ker (template n) ∧
        (fun x : s.ker => φ (p+x)) ∈ affinePullbackFamily s.ker (template n) ∧
        essentialDimension (fun x : s.ker => φ x) = 2^(n+2)-1 ∧
        essentialDimension (fun x : s.ker => φ (p+x)) = 2^(n+2)-1 ∧
        essentialDualSpace (fun x : s.ker => φ x) ⊓
          essentialDualSpace (fun x : s.ker => φ (p+x)) = ⊥ := by
  obtain ⟨⟨α,hα⟩,heqα⟩ := hφ
  obtain ⟨γ,hγ,hγ0,heqγ⟩ := exists_root_normalized_pullback n α hα
  have heq : (fun x => template (n+1) (γ x)) = φ := heqγ.trans heqα
  let s : Module.Dual (ZMod 2) U :=
    (LinearMap.fst (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n)).comp γ.linear
  have hsx (x : U) : (γ x).1 = s x := by
    have hh := congrArg Prod.fst (γ.map_vadd (0:U) x)
    change (γ (x+0)).1 = (γ.linear x).1 + (γ 0).1 at hh
    change (γ x).1 = (γ.linear x).1
    simpa [hγ0] using hh
  have hs : Function.Surjective s := by
    intro c
    obtain ⟨x,hx⟩ := hγ (c,0,0)
    exact ⟨x,(hsx x).symm.trans (congrArg Prod.fst hx)⟩
  have hsne : s ≠ 0 := by
    intro h
    obtain ⟨x,hx⟩ := hs 1
    simpa [h] using hx
  obtain ⟨p,hp⟩ := hs 1
  let L : TemplateSpace (n+1) →ₗ[ZMod 2] TemplateSpace n :=
    (LinearMap.fst (ZMod 2) (TemplateSpace n) (TemplateSpace n)).comp
      (LinearMap.snd (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n))
  let R : TemplateSpace (n+1) →ₗ[ZMod 2] TemplateSpace n :=
    (LinearMap.snd (ZMod 2) (TemplateSpace n) (TemplateSpace n)).comp
      (LinearMap.snd (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n))
  let inc : s.ker →ᵃ[ZMod 2] U := s.ker.subtype.toAffineMap
  let a : s.ker →ᵃ[ZMod 2] TemplateSpace n := (L.toAffineMap.comp γ).comp inc
  let b : s.ker →ᵃ[ZMod 2] TemplateSpace n := (R.toAffineMap.comp γ).comp
    (AffineMap.const (ZMod 2) s.ker p + inc)
  have hab : Function.Surjective (a.linear.prod b.linear) := by
    rintro ⟨u,v⟩
    obtain ⟨x,hx⟩ := (γ.linear_surjective_iff.mpr hγ) (0,u,v)
    have hx0 : s x = 0 := congrArg Prod.fst hx
    refine ⟨⟨x,hx0⟩, ?_⟩
    apply Prod.ext
    · exact congrArg (fun y => y.2.1) hx
    · simpa [b,R,inc,LinearMap.comp_apply,LinearMap.snd] using
        congrArg (fun y => y.2.2) hx
  have ha : Function.Surjective a := by
    apply a.linear_surjective_iff.mp
    intro u
    obtain ⟨x,hx⟩ := hab (u,0)
    exact ⟨x,congrArg Prod.fst hx⟩
  have hb : Function.Surjective b := by
    apply b.linear_surjective_iff.mp
    intro v
    obtain ⟨x,hx⟩ := hab (0,v)
    exact ⟨x,congrArg Prod.snd hx⟩
  have heqa : (fun x => template n (a x)) = (fun x : s.ker => φ x) := by
    funext x
    have hx0 : (γ x).1 = 0 := (hsx x).trans x.property
    change template n (γ x).2.1 = φ x
    simpa [template,branch,hx0] using congrFun heq x
  have heqb : (fun x => template n (b x)) = (fun x : s.ker => φ (p+x)) := by
    funext x
    have hx1 : (γ (p+x)).1 = 1 := by rw [hsx,map_add,hp,x.property,add_zero]
    change template n (γ (p+x)).2.2 = φ (p+x)
    simpa [template,branch,hx1] using congrFun heq (p+x)
  have hea := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) a ha
  have heb := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) b hb
  have hda := essentialDimension_affineMap_precompose_periodFree
    (template n) (template_period_iff n) a ha
  have hdb := essentialDimension_affineMap_precompose_periodFree
    (template n) (template_period_iff n) b hb
  rw [heqa] at hea hda
  rw [heqb] at heb hdb
  rw [templateSpace_finrank] at hda hdb
  refine ⟨s,hsne,p,hp,⟨⟨a,ha⟩,heqa⟩,⟨⟨b,hb⟩,heqb⟩,hda,hdb,?_⟩
  rw [hea,heb]
  exact (jointSurjective_iff_disjoint_dualAnnihilator a.linear b.linear
    (a.linear_surjective_iff.mpr ha) (b.linear_surjective_iff.mpr hb)).mp hab

/-- The paper's intrinsic height-`n+2` trees are exactly the existing
surjective affine pullbacks of `template n`. This is the public bridge used
to transfer balance, flats, quotient invariance, and exact support counts.
The height-two clause is the literal balance/degree/essential-dimension
definition, with its degree-free equivalence used in the base case. -/
theorem isTreeFunction_iff_affinePullbackFamily [Finite U] (n : ℕ) (φ : U → ZMod 2) :
    IsTreeFunction (n+2) φ ↔ φ ∈ affinePullbackFamily U (template n) := by
  induction n generalizing U with
  | zero => exact isHeightTwoTree_iff_mem_affinePullbackFamily φ
  | succ n ih =>
    constructor
    · intro hφ
      change IsTreeFunction (n+3) φ at hφ
      obtain ⟨s,hs,p,hp,L₀,L₁,hd₀,hd₁,hdisj,h₀,hE₀,h₁,hE₁⟩ := hφ
      apply mem_affinePullbackFamily_of_intrinsic_root n φ s p hp
        ((ih _).mp h₀) ((ih _).mp h₁)
      rw [hE₀,hE₁]
      exact hdisj
    · intro hφ
      obtain ⟨s,hs,p,hp,h₀,h₁,hd₀,hd₁,hdisj⟩ :=
        exists_intrinsic_root_of_affinePullbackFamily n φ hφ
      change IsTreeFunction (n+3) φ
      exact ⟨s,hs,p,hp,essentialDualSpace (fun x : s.ker => φ x),
        essentialDualSpace (fun x : s.ker => φ (p+x)),
        hd₀,hd₁,hdisj,(ih _).mpr h₀,rfl,(ih _).mpr h₁,rfl⟩

end BinaryFieldCounterexamples.Trees
