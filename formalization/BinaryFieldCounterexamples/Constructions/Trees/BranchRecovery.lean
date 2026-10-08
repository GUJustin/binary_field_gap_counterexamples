/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AffineOrbits
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Recovering the root branch from translation periods

The true branching hyperplane has a full child space of periods. Every other
hyperplane has fewer: if both child functionals are nonzero, its period space
injects into the single branch bit; if only one is nonzero, periods inject into
that functional's proper kernel. This gives an elementary recovery argument
without assuming a highest-degree or exterior-algebra identity.

For an affine stabilizer, pull back the root hyperplane by its linear part. The
unused output child embeds in the periods of the restricted function, so the
recovery bound forces preservation of the root linear functional.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def periodSubmodule (f : V → ZMod 2) : Submodule (ZMod 2) V := by
  refine {
    carrier := {u | IsPeriod f u}
    zero_mem' := by intro x; simp
    add_mem' := by
      intro u v hu hv x
      rw [←add_assoc,hv,hu]
    smul_mem' := ?_ }
  intro a u hu
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) a with rfl | rfl
  · simpa using (show IsPeriod f 0 from fun x => by simp)
  · simpa using hu

theorem mem_periodSubmodule (f : V → ZMod 2) (u : V) :
    u ∈ periodSubmodule f ↔ IsPeriod f u := by
  rfl

def branchFunctional (a : ZMod 2) (b c : Dual (ZMod 2) V) :
    (ZMod 2 × V × V) →ₗ[ZMod 2] ZMod 2 := by
  refine { toFun := fun x => a*x.1+b x.2.1+c x.2.2, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    simp only [Prod.fst_add,Prod.snd_add,map_add]
    ring
  · intro t x
    change a*(t*x.1)+b (t • x.2.1)+c (t • x.2.2)=t*(a*x.1+b x.2.1+c x.2.2)
    simp only [map_smul,smul_eq_mul]
    ring

theorem branchFunctional_apply (a : ZMod 2) (b c : Dual (ZMod 2) V) (x : ZMod 2 × V × V) :
    branchFunctional a b c x=a*x.1+b x.2.1+c x.2.2 := by
  rfl

theorem branch_restricted_period_zero_of_first_zero
    (f g : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0) (hg : ∀ u, IsPeriod g u → u=0)
    (a : ZMod 2) (b c : Dual (ZMod 2) V) (hb : Function.Surjective b) (hc : Function.Surjective c)
    (u : (branchFunctional a b c).ker)
    (hu : IsPeriod (fun x : (branchFunctional a b c).ker => branch f g (x : ZMod 2 × V × V)) u)
    (huz : (u : ZMod 2 × V × V).1=0) : u=0 := by
  have huf : IsPeriod f (u : ZMod 2 × V × V).2.1 := by
    intro x
    obtain ⟨y,hy⟩ := hc (-b x)
    have hm : (0,x,y) ∈ (branchFunctional a b c).ker := by
      change a*0+b x+c y=0
      rw [hy]; ring
    have h := hu ⟨(0,x,y),hm⟩
    simpa [branch,huz] using h
  have hug : IsPeriod g (u : ZMod 2 × V × V).2.2 := by
    intro y
    obtain ⟨x,hx⟩ := hb (-a-c y)
    have hm : (1,x,y) ∈ (branchFunctional a b c).ker := by
      change a*1+b x+c y=0
      rw [hx]; ring
    have h := hu ⟨(1,x,y),hm⟩
    simpa [branch,huz] using h
  apply Subtype.ext
  exact Prod.ext huz (Prod.ext (hf _ huf) (hg _ hug))
theorem card_branch_restricted_periods_le_two [Fintype V]
    (f g : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0) (hg : ∀ u, IsPeriod g u → u=0)
    (a : ZMod 2) (b c : Dual (ZMod 2) V) (hb : Function.Surjective b) (hc : Function.Surjective c) :
    Nat.card (periodSubmodule (fun x : (branchFunctional a b c).ker => branch f g (x : ZMod 2 × V × V)))≤2 := by
  let H := (branchFunctional a b c).ker
  let Q := periodSubmodule (fun x : H => branch f g (x : ZMod 2 × V × V))
  let l : Q → ZMod 2 := fun u => ((u : H) : ZMod 2 × V × V).1
  have hi : Function.Injective l := by
    intro u v huv
    have hper : IsPeriod (fun x : H => branch f g (x : ZMod 2 × V × V)) ((u:H)-(v:H)) :=
      Q.sub_mem u.property v.property
    have hz : (((u:H)-(v:H) : H) : ZMod 2 × V × V).1=0 := by
      change ((u:H) : ZMod 2 × V × V).1-((v:H) : ZMod 2 × V × V).1=0
      exact sub_eq_zero.mpr huv
    have he := branch_restricted_period_zero_of_first_zero f g hf hg a b c hb hc _ hper hz
    exact Subtype.ext (sub_eq_zero.mp he)
  have hcard := Nat.card_le_card_of_injective l hi
  simpa [Nat.card_eq_fintype_card] using hcard
theorem branch_left_slice_period_coordinates
    (f g : V → ZMod 2) (hg : ∃ x y, g x≠g y)
    (hgp : ∀ u, IsPeriod g u → u=0)
    (a : ZMod 2) (b : Dual (ZMod 2) V) (hb : Function.Surjective b)
    (u : (branchFunctional a b 0).ker)
    (hu : IsPeriod (fun x : (branchFunctional a b 0).ker => branch f g (x : ZMod 2 × V × V)) u) :
    (u : ZMod 2 × V × V).1=0 ∧ (u : ZMod 2 × V × V).2.2=0 := by
  have hz : (u : ZMod 2 × V × V).1=0 := by
    by_contra hn
    obtain ⟨y₀,y₁,hy⟩ := hg
    have hm (y : V) : (0,0,y) ∈ (branchFunctional a b 0).ker := by
      change a*0+b 0+0=0
      simp
    have h₀ := hu ⟨(0,0,y₀-(u : ZMod 2 × V × V).2.2),hm _⟩
    have h₁ := hu ⟨(0,0,y₁-(u : ZMod 2 × V × V).2.2),hm _⟩
    simp [branch,hn] at h₀ h₁
    exact hy (h₀.trans h₁.symm)
  refine ⟨hz,hgp _ ?_⟩
  intro y
  obtain ⟨x,hx⟩ := hb (-a)
  have hm : (1,x,y) ∈ (branchFunctional a b 0).ker := by
    change a*1+b x+0=0
    rw [hx]; ring
  have h := hu ⟨(1,x,y),hm⟩
  simpa [branch,hz] using h

theorem branch_right_slice_period_coordinates
    (f g : V → ZMod 2) (hf : ∃ x y, f x≠f y)
    (hfp : ∀ u, IsPeriod f u → u=0)
    (a : ZMod 2) (c : Dual (ZMod 2) V)
    (u : (branchFunctional a 0 c).ker)
    (hu : IsPeriod (fun x : (branchFunctional a 0 c).ker => branch f g (x : ZMod 2 × V × V)) u) :
    (u : ZMod 2 × V × V).1=0 ∧ (u : ZMod 2 × V × V).2.1=0 := by
  have hz : (u : ZMod 2 × V × V).1=0 := by
    by_contra hn
    obtain ⟨x₀,x₁,hx⟩ := hf
    have hm (x : V) : (0,x,0) ∈ (branchFunctional a 0 c).ker := by
      change a*0+0+c 0=0
      simp
    have h₀ := hu ⟨(0,x₀,0),hm _⟩
    have h₁ := hu ⟨(0,x₁,0),hm _⟩
    simp [branch,hn] at h₀ h₁
    exact hx (h₀.symm.trans h₁)
  refine ⟨hz,hfp _ ?_⟩
  intro x
  have hm : (0,x,0) ∈ (branchFunctional a 0 c).ker := by
    change a*0+0+c 0=0
    simp
  have h := hu ⟨(0,x,0),hm⟩
  simpa [branch,hz] using h
theorem card_branch_left_slice_periods_lt [Fintype V]
    (f g : V → ZMod 2) (hg : ∃ x y, g x≠g y) (hgp : ∀ u, IsPeriod g u → u=0)
    (a : ZMod 2) (b : Dual (ZMod 2) V) (hb : Function.Surjective b) :
    Nat.card (periodSubmodule (fun x : (branchFunctional a b 0).ker => branch f g (x : ZMod 2 × V × V)))<Nat.card V := by
  classical
  let H := (branchFunctional a b 0).ker
  let Q := periodSubmodule (fun x : H => branch f g (x : ZMod 2 × V × V))
  letI : Fintype Q := Fintype.ofFinite Q
  let l : Q → V := fun u => ((u:H) : ZMod 2 × V × V).2.1
  have hcoords (u : Q) := branch_left_slice_period_coordinates f g hg hgp a b hb (u:H) u.property
  have hi : Function.Injective l := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hcoords u).1.trans (hcoords v).1.symm)
      (Prod.ext huv ((hcoords u).2.trans (hcoords v).2.symm))
  have hz (u : Q) : b (l u)=0 := by
    have h := (u:H).property
    change a*((u:H) : ZMod 2 × V × V).1+b (l u)+0=0 at h
    simpa only [(hcoords u).1,mul_zero,zero_add,add_zero] using h
  have hns : ¬Function.Surjective l := by
    intro hs
    obtain ⟨x,hx⟩ := hb 1
    obtain ⟨u,rfl⟩ := hs x
    exact zero_ne_one ((hz u).symm.trans hx)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_not_surjective l hi hns

theorem card_branch_right_slice_periods_lt [Fintype V]
    (f g : V → ZMod 2) (hf : ∃ x y, f x≠f y) (hfp : ∀ u, IsPeriod f u → u=0)
    (a : ZMod 2) (c : Dual (ZMod 2) V) (hc : Function.Surjective c) :
    Nat.card (periodSubmodule (fun x : (branchFunctional a 0 c).ker => branch f g (x : ZMod 2 × V × V)))<Nat.card V := by
  classical
  let H := (branchFunctional a 0 c).ker
  let Q := periodSubmodule (fun x : H => branch f g (x : ZMod 2 × V × V))
  letI : Fintype Q := Fintype.ofFinite Q
  let l : Q → V := fun u => ((u:H) : ZMod 2 × V × V).2.2
  have hcoords (u : Q) := branch_right_slice_period_coordinates f g hf hfp a c (u:H) u.property
  have hi : Function.Injective l := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hcoords u).1.trans (hcoords v).1.symm)
      (Prod.ext ((hcoords u).2.trans (hcoords v).2.symm) huv)
  have hz (u : Q) : c (l u)=0 := by
    have h := (u:H).property
    change a*((u:H) : ZMod 2 × V × V).1+0+c (l u)=0 at h
    simpa only [(hcoords u).1,mul_zero,zero_add,add_zero] using h
  have hns : ¬Function.Surjective l := by
    intro hs
    obtain ⟨x,hx⟩ := hc 1
    obtain ⟨u,rfl⟩ := hs x
    exact zero_ne_one ((hz u).symm.trans hx)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_not_surjective l hi hns
theorem binary_functional_surjective_of_ne_zero (b : Dual (ZMod 2) V) (hb : b≠0) :
    Function.Surjective b := by
  have hex : ∃ x, b x≠0 := by
    by_contra! h
    apply hb
    ext x
    exact h x
  obtain ⟨x,hx⟩ := hex
  have hx1 : b x=1 := ((show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (b x)).resolve_left hx
  intro y
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) y with rfl | rfl
  · exact ⟨0,map_zero b⟩
  · exact ⟨x,hx1⟩

theorem branch_kernel_recovery [Fintype V]
    (f g : V → ZMod 2) (hf : ∃ x y, f x≠f y) (hg : ∃ x y, g x≠g y)
    (hfp : ∀ u, IsPeriod f u → u=0) (hgp : ∀ u, IsPeriod g u → u=0)
    (hV : 2<Nat.card V) (a : ZMod 2) (b c : Dual (ZMod 2) V)
    (hcount : Nat.card V≤Nat.card (periodSubmodule
      (fun x : (branchFunctional a b c).ker => branch f g (x : ZMod 2 × V × V)))) :
    b=0 ∧ c=0 := by
  by_cases hb : b=0
  · subst b
    refine ⟨rfl,?_⟩
    by_contra hc
    have h := card_branch_right_slice_periods_lt f g hf hfp a c (binary_functional_surjective_of_ne_zero c hc)
    omega
  · by_cases hc : c=0
    · subst c
      have h := card_branch_left_slice_periods_lt f g hg hgp a b (binary_functional_surjective_of_ne_zero b hb)
      omega
    · have h := card_branch_restricted_periods_le_two f g hfp hgp a b c
        (binary_functional_surjective_of_ne_zero b hb) (binary_functional_surjective_of_ne_zero c hc)
      omega
theorem exists_branchFunctional_eq (l : Dual (ZMod 2) (ZMod 2 × V × V)) :
    ∃ a b c, branchFunctional a b c=l := by
  let a := l (1,0,0)
  let b : Dual (ZMod 2) V := l.comp ((LinearMap.inr (ZMod 2) (ZMod 2) (V × V)).comp
    (LinearMap.inl (ZMod 2) V V))
  let c : Dual (ZMod 2) V := l.comp ((LinearMap.inr (ZMod 2) (ZMod 2) (V × V)).comp
    (LinearMap.inr (ZMod 2) V V))
  refine ⟨a,b,c,?_⟩
  apply LinearMap.ext
  intro x
  change a*x.1+b x.2.1+c x.2.2=l x
  have he : x=x.1 • (1,0,0)+(0,x.2.1,0)+(0,0,x.2.2) := by
    ext <;> simp
  conv_rhs => rw [he,map_add,map_add,map_smul]
  simp only [a,b,c,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,smul_eq_mul]
  ring

theorem affine_branch_kernel_period_lower [Fintype V]
    (f g : V → ZMod 2) (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (he : ∀ x, branch f g (e x)=branch f g x)
    (l : Dual (ZMod 2) (ZMod 2 × V × V)) (hl : ∀ x, l x=(e.linear x).1) :
    Nat.card V≤Nat.card (periodSubmodule (fun x : l.ker => branch f g (x : ZMod 2 × V × V))) := by
  classical
  let v : V → ZMod 2 × V × V := fun w => if (e 0).1=0 then (0,0,w) else (0,w,0)
  have hvz (w : V) : (v w).1=0 := by simp [v]; split_ifs <;> rfl
  have hv : Function.Injective v := by
    intro x y h
    dsimp [v] at h
    split_ifs at h
    · exact congrArg (fun z : ZMod 2 × V × V => z.2.2) h
    · exact congrArg (fun z : ZMod 2 × V × V => z.2.1) h
  have hm (w : V) : e.linear.symm (v w) ∈ l.ker := by
    change l (e.linear.symm (v w))=0
    rw [hl,e.linear.apply_symm_apply,hvz]
  have hperiod (w : V) : IsPeriod (fun x : l.ker => branch f g (x : ZMod 2 × V × V))
      (⟨e.linear.symm (v w),hm w⟩ : l.ker) := by
    intro x
    have hxz : (e (x : ZMod 2 × V × V)).1=(e 0).1 := by
      have hex := e.map_vadd 0 (x : ZMod 2 × V × V)
      have hxl : (e.linear (x : ZMod 2 × V × V)).1=0 := (hl _).symm.trans x.property
      simpa only [vadd_eq_add,add_zero,Prod.fst_add,hxl,zero_add] using congrArg Prod.fst hex
    have ha : e ((x : ZMod 2 × V × V)+e.linear.symm (v w))=e (x : ZMod 2 × V × V)+v w := by
      simpa [vadd_eq_add,add_comm] using e.map_vadd (x : ZMod 2 × V × V) (e.linear.symm (v w))
    change branch f g ((x : ZMod 2 × V × V)+e.linear.symm (v w))=branch f g (x : ZMod 2 × V × V)
    rw [←he _,←he (x : ZMod 2 × V × V),ha]
    simp only [branch,Prod.fst_add,hvz,add_zero,hxz,v]
    split_ifs <;> simp
  let j : V → periodSubmodule (fun x : l.ker => branch f g (x : ZMod 2 × V × V)) :=
    fun w => ⟨⟨e.linear.symm (v w),hm w⟩,hperiod w⟩
  apply Nat.card_le_card_of_injective j
  intro x y h
  apply hv
  apply e.linear.symm.injective
  have hh : e.linear.symm (v x)=e.linear.symm (v y) := congrArg (fun u : periodSubmodule (fun x : l.ker => branch f g (x : ZMod 2 × V × V)) => ((u : l.ker) : ZMod 2 × V × V)) h
  exact hh
theorem affine_branch_stabilizer_first_linear [Fintype V]
    (f g : V → ZMod 2) (hf : ∃ x y, f x≠f y) (hg : ∃ x y, g x≠g y)
    (hfp : ∀ u, IsPeriod f u → u=0) (hgp : ∀ u, IsPeriod g u → u=0)
    (hV : 2<Nat.card V)
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (he : ∀ x, branch f g (e x)=branch f g x) :
    ∀ x, (e.linear x).1=x.1 := by
  let l : Dual (ZMod 2) (ZMod 2 × V × V) :=
    (LinearMap.fst (ZMod 2) (ZMod 2) (V × V)).comp e.linear.toLinearMap
  have hl (x) : l x=(e.linear x).1 := rfl
  have hcount := affine_branch_kernel_period_lower f g e he l hl
  obtain ⟨a,b,c,hform⟩ := exists_branchFunctional_eq l
  have hcount' : Nat.card V≤Nat.card (periodSubmodule
      (fun x : (branchFunctional a b c).ker => branch f g (x : ZMod 2 × V × V))) := by
    rw [hform]
    exact hcount
  obtain ⟨rfl,rfl⟩ := branch_kernel_recovery f g hf hg hfp hgp hV a b c hcount'
  have hlin (x : ZMod 2 × V × V) : (e.linear x).1=a*x.1 := by
    have h := congrArg (fun k : Dual (ZMod 2) (ZMod 2 × V × V) => k x) hform
    simpa only [branchFunctional_apply,LinearMap.zero_apply,add_zero,hl] using h.symm
  have ha : a≠0 := by
    intro ha
    obtain ⟨x,hx⟩ := e.linear.surjective (1,0,0)
    have hh := hlin x
    rw [hx,ha] at hh
    simpa using hh
  have ha1 : a=1 := ((show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) a).resolve_left ha
  intro x
  simpa only [ha1,one_mul] using hlin x
end BinaryFieldCounterexamples.Trees
