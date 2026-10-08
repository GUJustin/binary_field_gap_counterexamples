/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FunctionalInterpolants
/-!
# Minimal balanced Boolean decision-tree templates

The height-two template is the concrete function `ab+c`. Higher templates
branch on one new binary coordinate and use independent child coordinates.
Literal fiber counts prove balance; translation periods are zero in the minimal
space and exactly the kernel after any surjective linear pullback. No family
count or uniqueness of a recursive description is assumed here.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
/-- A literal translation period of a binary function. -/
def IsPeriod {V : Type*} [Add V] (f : V → ZMod 2) (u : V) : Prop :=
  ∀ x, f (x+u)=f x
/-- Branch on one binary coordinate, using disjoint child coordinates. -/
def branch {V W : Type*} (f : V → ZMod 2) (g : W → ZMod 2) (x : ZMod 2 × V × W) : ZMod 2 :=
  if x.1=0 then f x.2.1 else g x.2.2
/-- A period cannot exchange two independent nonconstant child functions. -/
theorem branch_period_iff {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (f : V → ZMod 2) (g : W → ZMod 2)
    (hf : ∃ x y, f x≠f y) (u : ZMod 2 × V × W) :
    IsPeriod (branch f g) u ↔ u.1=0 ∧ IsPeriod f u.2.1 ∧ IsPeriod g u.2.2 := by
  constructor
  · intro h
    have hz : u.1=0 := by
      by_contra hu
      obtain ⟨x,y,hxy⟩ := hf
      have hx := h (0,x,0)
      have hy := h (0,y,0)
      simp only [branch,Prod.fst_add,Prod.snd_add,zero_add,ite_eq_right hu] at hx hy
      exact hxy (hx.symm.trans hy)
    refine ⟨hz,?_,?_⟩
    · intro x
      simpa [branch,hz] using h (0,x,0)
    · intro y
      simpa [branch,hz] using h (1,0,y)
  · rintro ⟨hz,hf,hg⟩ x
    dsimp [branch]
    simp only [hz,add_zero]
    split_ifs
    · exact hf x.2.1
    · exact hg x.2.2
/-- Independent branching multiplies the two child fiber sizes by the unused coordinates. -/
theorem branch_fiber_card {V W : Type*} [Fintype V] [Fintype W]
    (f : V → ZMod 2) (g : W → ZMod 2) (b : ZMod 2) :
    Nat.card {x : ZMod 2 × V × W // branch f g x=b}=
      Nat.card {x : V // f x=b}*Fintype.card W+Fintype.card V*Nat.card {y : W // g y=b} := by
  classical
  let e : ({x : V // f x=b} × W) ⊕ (V × {y : W // g y=b}) ≃
      {x : ZMod 2 × V × W // branch f g x=b} :=
    { toFun := fun x => match x with
        | Sum.inl x => ⟨(0,x.1,x.2),by simpa [branch] using x.1.property⟩
        | Sum.inr x => ⟨(1,x.1,x.2),by simpa [branch] using x.2.property⟩
      invFun := fun x => if h : x.1.1=0 then
        Sum.inl (⟨x.1.2.1,by simpa [branch,h] using x.property⟩,x.1.2.2)
        else Sum.inr (x.1.2.1,⟨x.1.2.2,by simpa [branch,h] using x.property⟩)
      left_inv := by rintro (x|x) <;> simp
      right_inv := by
        intro x
        dsimp only
        split_ifs with h
        · apply Subtype.ext
          exact Prod.ext h.symm rfl
        · have h1 : x.1.1=1 := by
            exact ((show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) x.1.1).resolve_left h
          apply Subtype.ext
          exact Prod.ext h1.symm rfl }
  rw [←Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_prod]
/-- The minimal height-two balanced quadratic template. -/
def baseTemplate (x : Fin 3 → ZMod 2) : ZMod 2 := x 0*x 1+x 2
/-- The height-two template has no nonzero period. -/
theorem baseTemplate_period_iff (u : Fin 3 → ZMod 2) : IsPeriod baseTemplate u ↔ u=0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h ![0,1,0]
    have h2 := h ![1,0,0]
    simp [baseTemplate] at h0 h1 h2
    have hu0 : u 0=0 := by linear_combination h1-h0
    have hu1 : u 1=0 := by linear_combination h2-h0
    have hu2 : u 2=0 := by simpa [hu0,hu1] using h0
    ext i
    fin_cases i <;> assumption
  · rintro rfl x
    simp
/-- Each value of the base template occurs four times. -/
theorem baseTemplate_fiber_card (b : ZMod 2) : Nat.card {x : Fin 3 → ZMod 2 // baseTemplate x=b}=4 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases b <;> decide
/-- Minimal coordinate space at height `n+2`, with disjoint recursive children. -/
def TemplateSpace : ℕ → Type
  | 0 => Fin 3 → ZMod 2
  | n+1 => ZMod 2 × TemplateSpace n × TemplateSpace n
/-- The template space inherits componentwise addition. -/
def templateSpaceAddCommGroup (n : ℕ) : AddCommGroup (TemplateSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (AddCommGroup (Fin 3 → ZMod 2))
  | succ n ih => letI := ih; exact inferInstanceAs (AddCommGroup (ZMod 2 × TemplateSpace n × TemplateSpace n))
attribute [local instance] templateSpaceAddCommGroup

/-- The template space is a binary vector space. -/
def templateSpaceModule (n : ℕ) : Module (ZMod 2) (TemplateSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (Module (ZMod 2) (Fin 3 → ZMod 2))
  | succ n ih => letI := ih; exact inferInstanceAs (Module (ZMod 2) (ZMod 2 × TemplateSpace n × TemplateSpace n))
attribute [local instance] templateSpaceModule

/-- The concrete template coordinates are finite. -/
def templateSpaceFintype (n : ℕ) : Fintype (TemplateSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 3 → ZMod 2))
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (ZMod 2 × TemplateSpace n × TemplateSpace n))
attribute [local instance] templateSpaceFintype

/-- The literal minimal balanced decision-tree template. -/
def template : (n : ℕ) → TemplateSpace n → ZMod 2
  | 0 => baseTemplate
  | n+1 => branch (template n) (template n)
/-- Every template attains both binary values. -/
theorem template_surjective (n : ℕ) : Function.Surjective (template n) := by
  induction n with
  | zero =>
    intro b
    exact ⟨![0,0,b],by simp [template,baseTemplate]⟩
  | succ n ih =>
    intro b
    obtain ⟨x,hx⟩ := ih b
    exact ⟨(0,x,0),by simpa [template,branch] using hx⟩
/-- Minimal templates have no nonzero translation periods. -/
theorem template_period_iff (n : ℕ) (u : TemplateSpace n) : IsPeriod (template n) u ↔ u=0 := by
  induction n with
  | zero => exact baseTemplate_period_iff u
  | succ n ih =>
    obtain ⟨x,hx⟩ := template_surjective n 0
    obtain ⟨y,hy⟩ := template_surjective n 1
    change IsPeriod (branch (template n) (template n)) (u : ZMod 2 × TemplateSpace n × TemplateSpace n) ↔ u=0
    apply (branch_period_iff (template n) (template n) ⟨x,y,by rw [hx,hy]; decide⟩ u).trans
    rw [ih,ih]
    exact ⟨fun h => Prod.ext h.1 (Prod.ext h.2.1 h.2.2),fun h => by subst u; exact ⟨rfl,rfl,rfl⟩⟩
/-- Minimal template dimension is the exact decision-tree coordinate count. -/
theorem templateSpace_card (n : ℕ) : Fintype.card (TemplateSpace n)=2^(2^(n+2)-1) := by
  induction n with
  | zero =>
    change Fintype.card (Fin 3 → ZMod 2)=_
    norm_num [Fintype.card_fun]
  | succ n ih =>
    change Fintype.card (ZMod 2 × TemplateSpace n × TemplateSpace n)=_
    rw [Fintype.card_prod,Fintype.card_prod,ZMod.card,ih]
    have hp : 1≤(2:ℕ)^(n+2) := Nat.one_le_pow _ _ (by decide)
    rw [show 2^(n+1+2)-1=1+(2^(n+2)-1)+(2^(n+2)-1) by
      rw [show n+1+2=n+2+1 by omega,pow_succ]; omega]
    simp only [pow_add,pow_one]
    ring
/-- Every minimal decision-tree template is exactly balanced. -/
theorem template_fiber_card (n : ℕ) (b : ZMod 2) :
    Nat.card {x : TemplateSpace n // template n x=b}=2^(2^(n+2)-2) := by
  induction n with
  | zero => exact baseTemplate_fiber_card b
  | succ n ih =>
    change Nat.card {x : ZMod 2 × TemplateSpace n × TemplateSpace n // branch (template n) (template n) x=b}=_
    rw [branch_fiber_card,ih,templateSpace_card]
    have hp : 2≤(2:ℕ)^(n+2) := by
      calc
        2=2^1 := by norm_num
        _≤_ := Nat.pow_le_pow_right (by decide) (by omega)
    rw [mul_comm (2^(2^(n+2)-1)) _,←two_mul,←pow_add,←pow_succ']
    congr 1
    have he : 2^(n+1+2)=2^(n+2)*2 := by
      rw [show n+1+2=n+2+1 by omega,pow_succ]
    omega
/-- Pulling a period-free template back along a surjective linear map gives exactly its kernel as period space. -/
theorem template_pullback_period_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (L : V →ₗ[ZMod 2] TemplateSpace n) (hL : Function.Surjective L) (u : V) :
    IsPeriod (fun x => template n (L x)) u ↔ L u=0 := by
  constructor
  · intro h
    apply (template_period_iff n (L u)).mp
    intro y
    obtain ⟨x,rfl⟩ := hL y
    simpa only [map_add] using h x
  · intro hu x
    simp only [map_add,hu,add_zero]
end BinaryFieldCounterexamples.Trees

