/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Templates
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
/-!
# Literal affine leaves of balanced templates

Each path is defined by a surjective binary linear constraint map. Its target
fixes the branch choices and output bit, so its fiber is an actual affine flat.
The path is uniquely recovered from every input, giving disjointness and the
exact union decomposition. Rank-nullity gives codimension equal to tree height.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Linear constraints for one root-to-leaf path. -/
def leafConstraint : (n : ℕ) → (Fin (n+1) → ZMod 2) → TemplateSpace n → (Fin (n+2) → ZMod 2)
  | 0,s,x => ![x 0,s 0*x 1+x 2]
  | n+1,s,x => Fin.cons x.1 (leafConstraint n (fun i => s i.succ)
      (if s 0=0 then x.2.1 else x.2.2))
/-- The affine target fixes the branch choices and the final binary value. -/
def leafTarget : (n : ℕ) → (Fin (n+1) → ZMod 2) → ZMod 2 → (Fin (n+2) → ZMod 2)
  | 0,s,b => ![s 0,b]
  | n+1,s,b => Fin.cons (s 0) (leafTarget n (fun i => s i.succ) b)
/-- Constraints on a fixed path are additive. -/
theorem leafConstraint_add (n : ℕ) (s : Fin (n+1) → ZMod 2) (x y : TemplateSpace n) :
    leafConstraint n s (x+y)=leafConstraint n s x+leafConstraint n s y := by
  induction n with
  | zero =>
    ext i
    fin_cases i
    · change x 0+y 0=x 0+y 0
      rfl
    · change s 0*(x 1+y 1)+(x 2+y 2)=(s 0*x 1+x 2)+(s 0*y 1+y 2)
      ring
  | succ n ih =>
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change leafConstraint n (fun i => s i.succ) (if s 0=0 then x.2.1+y.2.1 else x.2.2+y.2.2) j=
        leafConstraint n (fun i => s i.succ) (if s 0=0 then x.2.1 else x.2.2) j+
        leafConstraint n (fun i => s i.succ) (if s 0=0 then y.2.1 else y.2.2) j
      split_ifs <;> exact congrFun (ih _ _ _) j
/-- Path constraints as an actual binary linear map. -/
def leafConstraintLinear (n : ℕ) (s : Fin (n+1) → ZMod 2) :
    TemplateSpace n →ₗ[ZMod 2] (Fin (n+2) → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := leafConstraint n s
      map_zero' := by
        have h := leafConstraint_add n s 0 0
        simpa using (add_left_cancel (show leafConstraint n s 0+leafConstraint n s 0=leafConstraint n s 0+0 by simpa using h.symm))
      map_add' := leafConstraint_add n s }
/-- Every affine leaf target is attained: its linear constraint map is surjective. -/
theorem leafConstraint_surjective (n : ℕ) (s : Fin (n+1) → ZMod 2) :
    Function.Surjective (leafConstraint n s) := by
  induction n with
  | zero =>
    intro y
    refine ⟨![y 0,0,y 1],?_⟩
    ext i
    fin_cases i <;> simp [leafConstraint]
  | succ n ih =>
    intro y
    obtain ⟨x,hx⟩ := ih (fun i => s i.succ) (fun i => y i.succ)
    refine ⟨(y 0,x,x),?_⟩
    simp only [leafConstraint,ite_self,hx]
    exact Fin.cons_self_tail y
/-- Each point has one literal path through the recursive independent branches. -/
def leafPath : (n : ℕ) → TemplateSpace n → (Fin (n+1) → ZMod 2)
  | 0,x => ![x 0]
  | n+1,x => Fin.cons x.1 (leafPath n (if x.1=0 then x.2.1 else x.2.2))
/-- The leaf equations recover exactly the path and the template value. -/
theorem leafConstraint_eq_target_iff (n : ℕ) (s : Fin (n+1) → ZMod 2)
    (x : TemplateSpace n) (b : ZMod 2) :
    leafConstraint n s x=leafTarget n s b ↔ s=leafPath n x ∧ template n x=b := by
  induction n with
  | zero =>
    constructor
    · intro h
      have h0 : x 0=s 0 := congrFun h 0
      have h1 : s 0*x 1+x 2=b := congrFun h 1
      refine ⟨?_,?_⟩
      · ext i; fin_cases i; exact h0.symm
      · change x 0*x 1+x 2=b
        rwa [h0]
    · rintro ⟨hs,h⟩
      have h0 : s 0=x 0 := congrFun hs 0
      ext i
      fin_cases i
      · exact h0.symm
      · change s 0*x 1+x 2=b
        rw [h0]
        exact h
  | succ n ih =>
    simp only [leafConstraint,leafTarget,Fin.cons_inj]
    constructor
    · rintro ⟨hz,h⟩
      rw [←hz] at h
      obtain ⟨hs,hb⟩ := (ih _ _).mp h
      refine ⟨?_,?_⟩
      · change s=Fin.cons x.1 _
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hz.symm
        · exact congrFun hs j
      · change (if x.1=0 then template n x.2.1 else template n x.2.2)=b
        split_ifs at hb ⊢ <;> exact hb
    · rintro ⟨hs,hb⟩
      have hz : s 0=x.1 := congrFun hs 0
      have hs' : (fun i => s i.succ)=leafPath n (if x.1=0 then x.2.1 else x.2.2) :=
        funext (fun i => congrFun hs i.succ)
      refine ⟨hz.symm,?_⟩
      rw [hz]
      apply (ih _ _).mpr
      refine ⟨hs',?_⟩
      change (if x.1=0 then template n x.2.1 else template n x.2.2)=b at hb
      split_ifs at hb ⊢ <;> exact hb
/-- A canonical point on each leaf, chosen from the proved surjective constraints. -/
noncomputable def leafOrigin (n : ℕ) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) : TemplateSpace n :=
  Classical.choose (leafConstraint_surjective n s (leafTarget n s b))
/-- The chosen origin satisfies the literal affine equations. -/
theorem leafOrigin_spec (n : ℕ) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    leafConstraint n s (leafOrigin n s b)=leafTarget n s b := by
  exact Classical.choose_spec (leafConstraint_surjective n s (leafTarget n s b))
/-- Each leaf is the actual translate of a binary linear kernel. -/
noncomputable def leafFlat (n : ℕ) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    AffineSubspace (ZMod 2) (TemplateSpace n) :=
  AffineSubspace.mk' (leafOrigin n s b) (LinearMap.ker (leafConstraintLinear n s))
/-- Membership in the affine leaf is exactly its path and output constraints. -/
theorem mem_leafFlat (n : ℕ) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) (x : TemplateSpace n) :
    x ∈ leafFlat n s b ↔ s=leafPath n x ∧ template n x=b := by
  rw [leafFlat,AffineSubspace.mem_mk',LinearMap.mem_ker]
  change leafConstraintLinear n s (x-leafOrigin n s b)=0 ↔ _
  rw [map_sub,sub_eq_zero]
  change leafConstraint n s x=leafConstraint n s (leafOrigin n s b) ↔ _
  rw [leafOrigin_spec,leafConstraint_eq_target_iff]
/-- The affine leaves are pairwise disjoint. -/
theorem leafFlat_pairwise_disjoint (n : ℕ) (b : ZMod 2) :
    Pairwise (fun s t : Fin (n+1) → ZMod 2 => Disjoint (leafFlat n s b : Set (TemplateSpace n)) (leafFlat n t b)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  exact hst (((mem_leafFlat n s b x).mp hs).1.trans ((mem_leafFlat n t b x).mp ht).1.symm)
/-- The template fiber is the union of exactly its affine leaf supports. -/
theorem template_fiber_eq_union_leafFlat (n : ℕ) (b : ZMod 2) :
    {x : TemplateSpace n | template n x=b}=⋃ s : Fin (n+1) → ZMod 2, (leafFlat n s b : Set (TemplateSpace n)) := by
  ext x
  simp only [Set.mem_iUnion]
  change template n x=b ↔ ∃ s, x ∈ leafFlat n s b
  simp only [mem_leafFlat]
  exact ⟨fun h => ⟨leafPath n x,rfl,h⟩,fun ⟨_,_,h⟩ => h⟩
/-- There are exactly `2^(h-1)` leaves at height `h=n+2`. -/
theorem leaf_index_card (n : ℕ) : Fintype.card (Fin (n+1) → ZMod 2)=2^(n+1) := by
  simp
/-- The minimal coordinate space has exactly its prescribed dimension. -/
theorem templateSpace_finrank (n : ℕ) : Module.finrank (ZMod 2) (TemplateSpace n)=2^(n+2)-1 := by
  apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
  dsimp only
  rw [←templateSpace_card,←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp [Nat.card_eq_fintype_card]
/-- Every leaf has the stated affine codimension `h=n+2`. -/
theorem leafFlat_direction_finrank (n : ℕ) (s : Fin (n+1) → ZMod 2) (b : ZMod 2) :
    Module.finrank (ZMod 2) (leafFlat n s b).direction=2^(n+2)-1-(n+2) := by
  rw [leafFlat,AffineSubspace.direction_mk']
  have hr : LinearMap.range (leafConstraintLinear n s)=⊤ :=
    LinearMap.range_eq_top.mpr (leafConstraint_surjective n s)
  have he := LinearMap.finrank_range_add_finrank_ker (leafConstraintLinear n s)
  rw [hr,finrank_top,Module.finrank_pi,Fintype.card_fin,templateSpace_finrank] at he
  omega
end BinaryFieldCounterexamples.Trees

