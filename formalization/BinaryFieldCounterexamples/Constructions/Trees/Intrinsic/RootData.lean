/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Structure
/-!
# Literal root data for the paper's trees

Definition 6.3 (Section 6.2) calls a nonzero functional a root when its two
children are trees with independent essential dual spaces. `IsTreeRoot` names
precisely those data. The coordinate theorem below supplies the independent
coordinates used in the proofs of Lemmas 6.4 and 6.5; it makes no uniqueness
claim. Uniqueness is proved by Boolean degree in `DegreeStructure`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

/-- A root in the literal sense of Definition 6.3. The height bound excludes
height two, where the root need not be unique. -/
def IsTreeRoot (h : ℕ) (φ : U → ZMod 2) (s : Module.Dual (ZMod 2) U) : Prop :=
  3 ≤ h ∧ s ≠ 0 ∧ ∃ p : U, s p = 1 ∧
    ∃ L₀ L₁ : Submodule (ZMod 2) (Module.Dual (ZMod 2) s.ker),
      Module.finrank (ZMod 2) L₀ = 2^(h-1)-1 ∧
      Module.finrank (ZMod 2) L₁ = 2^(h-1)-1 ∧
      L₀ ⊓ L₁ = ⊥ ∧
      IsTreeFunction (h-1) (fun x : s.ker => φ x) ∧
      essentialDualSpace (fun x : s.ker => φ x) = L₀ ∧
      IsTreeFunction (h-1) (fun x : s.ker => φ (p+x)) ∧
      essentialDualSpace (fun x : s.ker => φ (p+x)) = L₁

/-- A root functional is nonzero by definition. -/
theorem IsTreeRoot.nonzero {h : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot h φ s) : s ≠ 0 := by
  exact hs.2.1

/-- The recursive tree clause is exactly existence of literal root data. -/
theorem isTreeFunction_succ_iff_exists_root (n : ℕ) (φ : U → ZMod 2) :
    IsTreeFunction (n+3) φ ↔ ∃ s, IsTreeRoot (n+3) φ s := by
  simp only [IsTreeFunction, IsTreeRoot, show n+3-1=n+2 by omega,
    show 3≤n+3 by omega, true_and]

/-- Root data imply the parent tree predicate. -/
theorem IsTreeRoot.isTreeFunction {h : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot h φ s) : IsTreeFunction h φ := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  exact (isTreeFunction_succ_iff_exists_root n φ).mpr ⟨s,hs⟩

/-- Translating the input changes no essential dual coordinate. -/
theorem essentialDualSpace_translate (φ : U → ZMod 2) (u : U) :
    essentialDualSpace (fun x => φ (u+x))=essentialDualSpace φ := by
  have h := essentialDualSpace_affineEquiv_precompose φ
    (AffineEquiv.constVAdd (ZMod 2) U u)
  change essentialDualSpace (fun x => φ (u+x))=
    (essentialDualSpace φ).map (LinearMap.id : U →ₗ[ZMod 2] U).dualMap at h
  simpa using h

/-- Translation is an invertible affine change of coordinates (Lemma 6.4(2)). -/
theorem IsTreeFunction.translate {h : ℕ} {φ : U → ZMod 2}
    (hφ : IsTreeFunction h φ) (u : U) : IsTreeFunction h (fun x => φ (u+x)) := by
  letI : Fintype U := Fintype.ofFinite _
  exact hφ.affineMap_precompose (AffineEquiv.constVAdd (ZMod 2) U u).toAffineMap
    (AffineEquiv.constVAdd (ZMod 2) U u).surjective

/-- The one-slice can be parametrized from any chosen point on it. Changing
that point translates the child, preserving its tree predicate and essential
space; this is the recursive-step observation in the proof of Lemma 6.4. -/
theorem IsTreeRoot.children_at {n : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot (n+3) φ s)
    (p : U) (hp : s p=1) :
    IsTreeFunction (n+2) (fun x : s.ker => φ x) ∧
    IsTreeFunction (n+2) (fun x : s.ker => φ (p+x)) ∧
    essentialDualSpace (fun x : s.ker => φ x) ⊓
      essentialDualSpace (fun x : s.ker => φ (p+x))=⊥ := by
  obtain ⟨_,_,q,hq,L₀,L₁,_,_,hdisj,h₀,hE₀,h₁,hE₁⟩ := hs
  simp only [show n+3-1=n+2 by omega] at h₀ h₁
  let u : s.ker := ⟨p-q,by simp [map_sub,hp,hq]⟩
  have he : (fun x : s.ker => φ (q+((u+x : s.ker) : U)))=(fun x : s.ker => φ (p+x)) := by
    funext x
    change φ (q+((p-q)+x))=φ (p+x)
    congr 1
    abel
  have ht := h₁.translate u
  have hE := essentialDualSpace_translate (fun x : s.ker => φ (q+x)) u
  rw [he] at ht hE
  rw [hE₁] at hE
  exact ⟨h₀,ht,by rw [hE₀,hE]; exact hdisj⟩

/-- Coordinates adapted to a given intrinsic root. The selector is exactly the
original linear root, with zero affine offset. The two child blocks are onto
jointly, because their actual essential dual spaces intersect trivially. -/
theorem IsTreeRoot.coordinates {n : ℕ} {φ : U → ZMod 2}
    {s : Module.Dual (ZMod 2) U} (hs : IsTreeRoot (n+3) φ s) :
    ∃ a : U →ᵃ[ZMod 2] TemplateSpace (n+1), Function.Surjective a ∧
      (∀ x, (a x).1=s x) ∧ φ=(fun x => template (n+1) (a x)) := by
  letI := templateSpaceAddCommGroup n
  letI := templateSpaceModule n
  obtain ⟨_,_,p,hp,L₀,L₁,_,_,hdisj,h₀,hE₀,h₁,hE₁⟩ := hs
  simp only [show n+3-1=n+2 by omega] at h₀ h₁
  obtain ⟨⟨a,ha⟩,heqa⟩ := (isTreeFunction_iff_affinePullbackFamily n _).mp h₀
  obtain ⟨⟨b,hb⟩,heqb⟩ := (isTreeFunction_iff_affinePullbackFamily n _).mp h₁
  change (fun x => template n (a x)) = (fun x : s.ker => φ x) at heqa
  change (fun x => template n (b x)) = (fun x : s.ker => φ (p+x)) at heqb
  have hea := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) a ha
  have heb := essentialDualSpace_affineMap_precompose_periodFree
    (template n) (template_period_iff n) b hb
  rw [heqa,hE₀] at hea
  rw [heqb,hE₁] at heb
  rw [hea,heb] at hdisj
  have hab := (jointSurjective_iff_disjoint_dualAnnihilator a.linear b.linear
    (a.linear_surjective_iff.mpr ha) (b.linear_surjective_iff.mpr hb)).mpr hdisj
  refine ⟨treeRootAffineMap (T := TemplateSpace n) s p hp a b,
    treeRootAffineMap_surjective (T := TemplateSpace n) s p hp a b hab,
    fun _ => rfl,?_⟩
  funext x
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (s x) with hx | hx
  · change φ x = if s x = 0 then template n (a (treeRootProjection s p hp x))
      else template n (b (treeRootProjection s p hp x))
    rw [hx,ite_eq_left rfl]
    exact ((congrFun heqa (treeRootProjection s p hp x)).trans
      (by change φ (x-s x • p)=φ x; simp [hx])).symm
  · change φ x = if s x = 0 then template n (a (treeRootProjection s p hp x))
      else template n (b (treeRootProjection s p hp x))
    rw [hx,ite_eq_right one_ne_zero]
    exact ((congrFun heqb (treeRootProjection s p hp x)).trans
      (by change φ (p+(x-s x • p))=φ x; rw [hx,one_smul]; congr 1; abel)).symm

omit [Finite U] in
/-- At a fixed root and fixed point in the one-slice, the children are literal
restrictions, so both functions and both essential spaces are determined. -/
theorem treeRoot_children_determined (φ : U → ZMod 2)
    (s : Module.Dual (ZMod 2) U) (p : U)
    (f₀ f₁ g₀ g₁ : s.ker → ZMod 2)
    (hf₀ : ∀ x, f₀ x=φ x) (hf₁ : ∀ x, f₁ x=φ (p+x))
    (hg₀ : ∀ x, g₀ x=φ x) (hg₁ : ∀ x, g₁ x=φ (p+x)) :
    f₀=g₀ ∧ f₁=g₁ ∧ essentialDualSpace f₀=essentialDualSpace g₀ ∧
      essentialDualSpace f₁=essentialDualSpace g₁ := by
  have h₀ : f₀=g₀ := funext fun x => (hf₀ x).trans (hg₀ x).symm
  have h₁ : f₁=g₁ := funext fun x => (hf₁ x).trans (hg₁ x).symm
  exact ⟨h₀,h₁,congrArg essentialDualSpace h₀,congrArg essentialDualSpace h₁⟩

end BinaryFieldCounterexamples.Trees
