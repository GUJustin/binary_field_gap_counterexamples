/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Leaves
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingIntersections
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
/-!
# Balanced affine-flat support families on prescribed spaces

Surjective affine pullbacks preserve exact balance by uniform fibers. Every
leaf is an actual affine subspace of the prescribed domain, has codimension
equal to tree height and the resulting exact cardinality, and the leaves form
a disjoint union of the literal support.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Surjective affine maps pull arbitrary finite fibers back uniformly. -/
theorem affine_preimage_fiber_count {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) (f : W → ZMod 2) (b : ZMod 2) :
    Nat.card {x : V // f (a x)=b}*Fintype.card W=
      Nat.card {y : W // f y=b}*Fintype.card V := by
  classical
  let S := Finset.univ.filter (fun y : W => f (y+a 0)=b)
  have hc := Gold.card_preimage_mul_card_of_surjective_addHom a.linear.toAddMonoidHom
    (a.linear_surjective_iff.mpr ha) S
  have he (x : V) : a.linear x+a 0=a x := by simpa using (a.map_vadd (0:V) x).symm
  have hS : S.card=Nat.card {y : W // f y=b} := by
    rw [Nat.card_eq_fintype_card,←Fintype.card_subtype]
    exact Fintype.card_congr ((Equiv.addRight (a 0)).subtypeEquiv (fun _ => Iff.rfl))
  rw [hS] at hc
  simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,LinearMap.toAddMonoidHom_coe,he,Nat.card_eq_fintype_card,
    Fintype.card_subtype] using hc
/-- Every surjective affine pullback of a minimal template is exactly balanced. -/
theorem template_affine_pullback_balanced {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (ha : Function.Surjective a) (b : ZMod 2) :
    2*Nat.card {x : V // template n (a x)=b}=Fintype.card V := by
  have hc := affine_preimage_fiber_count a ha (template n) b
  rw [templateSpace_card,template_fiber_card] at hc
  have hpow : 2^(2^(n+2)-1)=2*2^(2^(n+2)-2) := by
    have hp : 2≤(2:ℕ)^(n+2) := by
      exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 1≤n+2)
    rw [show 2^(n+2)-1=(2^(n+2)-2)+1 by omega,pow_succ]
    omega
  rw [hpow] at hc
  have hp : 0<(2:ℕ)^(2^(n+2)-2) := by positivity
  nlinarith
/-- The concrete affine leaves pull back to literal affine flats on the prescribed space. -/
noncomputable def pullbackLeafFlat {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    AffineSubspace (ZMod 2) V := (leafFlat n s b).comap a
/-- Literal membership in a pulled-back leaf. -/
theorem mem_pullbackLeafFlat {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) (x : V) :
    x ∈ pullbackLeafFlat n a s b ↔ s=leafPath n (a x) ∧ template n (a x)=b := by
  exact mem_leafFlat n s b (a x)
/-- Pulled-back leaves are pairwise disjoint on the prescribed domain. -/
theorem pullbackLeafFlat_pairwise_disjoint {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (b : ZMod 2) :
    Pairwise (fun s t : Fin (n+1) → ZMod 2 => Disjoint (pullbackLeafFlat n a s b : Set V) (pullbackLeafFlat n a t b)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  exact hst (((mem_pullbackLeafFlat n a s b x).mp hs).1.trans ((mem_pullbackLeafFlat n a t b x).mp ht).1.symm)
/-- The whole pullback support is the exact union of its affine leaves. -/
theorem template_pullback_fiber_eq_union {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (b : ZMod 2) :
    {x : V | template n (a x)=b}=⋃ s : Fin (n+1) → ZMod 2, (pullbackLeafFlat n a s b : Set V) := by
  ext x
  simp only [Set.mem_iUnion]
  change template n (a x)=b ↔ ∃s, x ∈ pullbackLeafFlat n a s b
  simp only [mem_pullbackLeafFlat]
  exact ⟨fun h => ⟨leafPath n (a x),rfl,h⟩,fun ⟨_,_,h⟩ => h⟩
/-- Every pulled-back leaf is nonempty and has the actual composed linear kernel as direction. -/
theorem pullbackLeafFlat_direction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (ha : Function.Surjective a)
    (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    (pullbackLeafFlat n a s b : Set V).Nonempty ∧
      (pullbackLeafFlat n a s b).direction=LinearMap.ker ((leafConstraintLinear n s).comp a.linear) := by
  obtain ⟨x0,hx0⟩ := ha (leafOrigin n s b)
  have hflat : pullbackLeafFlat n a s b=
      AffineSubspace.mk' x0 (LinearMap.ker ((leafConstraintLinear n s).comp a.linear)) := by
    ext x
    rw [pullbackLeafFlat,AffineSubspace.mem_comap,leafFlat,AffineSubspace.mem_mk',AffineSubspace.mem_mk',
      LinearMap.mem_ker,LinearMap.mem_ker,LinearMap.comp_apply]
    rw [a.linearMap_vsub x x0,hx0]
  rw [hflat]
  exact ⟨AffineSubspace.mk'_nonempty _ _,AffineSubspace.direction_mk' _ _⟩
/-- Surjective pullbacks still have affine codimension equal to tree height. -/
theorem pullbackLeafFlat_direction_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (ha : Function.Surjective a)
    (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    Module.finrank (ZMod 2) (pullbackLeafFlat n a s b).direction=
      Module.finrank (ZMod 2) V-(n+2) := by
  rw [(pullbackLeafFlat_direction n a ha s b).2]
  let L := (leafConstraintLinear n s).comp a.linear
  have hL : Function.Surjective L := (leafConstraint_surjective n s).comp (a.linear_surjective_iff.mpr ha)
  have he := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL,finrank_top,Module.finrank_pi,Fintype.card_fin] at he
  change Module.finrank (ZMod 2) L.ker=_
  omega
/-- A nonempty affine subspace has the same cardinality as its direction. -/
theorem affineSubspace_card_direction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (A : AffineSubspace (ZMod 2) V) (hA : (A:Set V).Nonempty) : Nat.card A=Nat.card A.direction := by
  obtain ⟨x0,hx0⟩ := hA
  let e : A ≃ A.direction :=
    { toFun := fun x => ⟨(x:V)-x0,AffineSubspace.vsub_mem_direction x.property hx0⟩
      invFun := fun v => ⟨(v:V)+x0,AffineSubspace.vadd_mem_of_mem_direction v.property hx0⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp }
  exact Nat.card_congr e
/-- Each actual pulled-back affine leaf has exactly the prescribed flat size. -/
theorem pullbackLeafFlat_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (n : ℕ) (a : V →ᵃ[ZMod 2] TemplateSpace n) (ha : Function.Surjective a)
    (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    Nat.card (pullbackLeafFlat n a s b)=2^(Module.finrank (ZMod 2) V-(n+2)) := by
  rw [affineSubspace_card_direction _ (pullbackLeafFlat_direction n a ha s b).1,
    Module.natCard_eq_pow_finrank (K := ZMod 2),pullbackLeafFlat_direction_finrank n a ha s b]
  simp [Nat.card_eq_fintype_card]
end BinaryFieldCounterexamples.Trees
