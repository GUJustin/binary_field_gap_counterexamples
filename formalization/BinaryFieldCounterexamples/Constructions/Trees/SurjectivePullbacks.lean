/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AffineOrbits
public import Mathlib.LinearAlgebra.Isomorphisms
/-!
# Actual affine pullback families on prescribed spaces

A period-free minimal function recovers the kernel of every surjective affine
map from its pullback. Equal pullbacks therefore differ by a unique affine
stabilizer. The resulting literal parameter bijection proves the exact family
count, and translation coordinates separate the affine-surjection population
into the codomain size times the linear-surjection population.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
/-- A surjective affine pullback transports periods through its actual linear part. -/
theorem affineMap_precompose_period_iff (f : W → ZMod 2) (a : V →ᵃ[ZMod 2] W)
    (ha : Function.Surjective a) (u : V) :
    IsPeriod (fun x => f (a x)) u ↔ IsPeriod f (a.linear u) := by
  have he (x : V) : a (x+u)=a x+a.linear u := by
    simpa [add_comm] using a.map_vadd x u
  constructor
  · intro h x
    obtain ⟨y,rfl⟩ := ha x
    simpa only [he] using h y
  · intro h x
    dsimp only
    rw [he]
    exact h (a x)
/-- Equal pullbacks of a period-free function recover the entire common quotient kernel. -/
theorem affine_pullback_ker_eq (f : W → ZMod 2) (hf : ∀ u, IsPeriod f u ↔ u=0)
    (a b : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hab : (fun x => f (a x))=(fun x => f (b x))) : a.linear.ker=b.linear.ker := by
  ext u
  rw [LinearMap.mem_ker,LinearMap.mem_ker,←hf,←hf,
    ←affineMap_precompose_period_iff f a ha,←affineMap_precompose_period_iff f b hb,hab]
/-- Surjective affine maps with the same kernel differ by a genuine affine automorphism. -/
theorem exists_affineEquiv_comp_of_ker_eq (a b : V →ᵃ[ZMod 2] W)
    (ha : Function.Surjective a) (hb : Function.Surjective b) (hker : a.linear.ker=b.linear.ker) :
    ∃ e : W ≃ᵃ[ZMod 2] W, ∀ x, e (a x)=b x := by
  have hal : Function.Surjective a.linear := a.linear_surjective_iff.mpr ha
  have hbl : Function.Surjective b.linear := b.linear_surjective_iff.mpr hb
  let A := a.linear.quotKerEquivOfSurjective hal
  let B := b.linear.quotKerEquivOfSurjective hbl
  let L := A.symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans B)
  have hL (x : V) : L (a.linear x)=b.linear x := by
    simp only [L,A,B,LinearEquiv.trans_apply,LinearMap.quotKerEquivOfSurjective_symm_apply,
      Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨AffineEquiv.ofLinearEquiv L (a 0) (b 0),?_⟩
  intro x
  have ha0 : a x-a 0=a.linear x := by
    apply sub_eq_iff_eq_add.mpr
    simpa using a.map_vadd (0:V) x
  have hb0 : b.linear x+b 0=b x := by simpa using (b.map_vadd (0:V) x).symm
  simpa only [AffineEquiv.ofLinearEquiv_apply,vsub_eq_sub,vadd_eq_add,ha0,hL] using hb0
/-- Equal pullbacks differ by a unique actual stabilizer of the minimal function. -/
theorem existsUnique_stabilizer_of_pullback_eq (f : W → ZMod 2) (hf : ∀ u, IsPeriod f u ↔ u=0)
    (a b : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hab : (fun x => f (a x))=(fun x => f (b x))) :
    ∃! e : affineFunctionStabilizer f, ∀ x, (e:W ≃ᵃ[ZMod 2] W) (a x)=b x := by
  obtain ⟨e,he⟩ := exists_affineEquiv_comp_of_ker_eq a b ha hb (affine_pullback_ker_eq f hf a b ha hb hab)
  have hstab : e ∈ affineFunctionStabilizer f := by
    rw [mem_affineFunctionStabilizer]
    intro y
    obtain ⟨x,rfl⟩ := ha y
    rw [he]
    exact (congrFun hab x).symm
  refine ⟨⟨e,hstab⟩,he,?_⟩
  intro e' he'
  apply Subtype.ext
  apply AffineEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := ha y
  exact (he' x).trans (he x).symm
/-- All literal affine surjections onto a minimal template space. -/
def SurjectiveAffineMaps (V W : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] := {a : V →ᵃ[ZMod 2] W // Function.Surjective a}
/-- The actual family obtained by every surjective affine pullback. -/
def affinePullbackFamily (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    (f : W → ZMod 2) : Set (V → ZMod 2) :=
  Set.range (fun a : SurjectiveAffineMaps V W => fun x => f (a.1 x))
/-- Kernel recovery gives the exact finite pullback-family count, with its actual stabilizer denominator. -/
theorem affinePullbackFamily_card_mul_stabilizer (f : W → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u=0) :
    Nat.card (affinePullbackFamily V f)*Nat.card (affineFunctionStabilizer f)=
      Nat.card (SurjectiveAffineMaps V W) := by
  classical
  let rep (g : affinePullbackFamily V f) : SurjectiveAffineMaps V W := Classical.choose g.property
  have hrep (g : affinePullbackFamily V f) : (fun x => f ((rep g).1 x))=g.1 :=
    Classical.choose_spec g.property
  let Ψ : affinePullbackFamily V f × affineFunctionStabilizer f → SurjectiveAffineMaps V W :=
    fun p => ⟨p.2.1.toAffineMap.comp (rep p.1).1,p.2.1.surjective.comp (rep p.1).2⟩
  have hΨ (p : affinePullbackFamily V f × affineFunctionStabilizer f) :
      (fun x => f ((Ψ p).1 x))=p.1.1 := by
    funext x
    change f (p.2.1 ((rep p.1).1 x))=p.1.1 x
    rw [(mem_affineFunctionStabilizer f p.2.1).mp p.2.2]
    exact congrFun (hrep p.1) x
  have hbij : Function.Bijective Ψ := by
    constructor
    · rintro ⟨g,e⟩ ⟨g',e'⟩ h
      have hg : g=g' := by
        apply Subtype.ext
        exact (hΨ (g,e)).symm.trans ((congrArg (fun a : SurjectiveAffineMaps V W => fun x => f (a.1 x)) h).trans (hΨ (g',e')))
      subst g'
      apply congrArg (fun e : affineFunctionStabilizer f => (g,e))
      apply Subtype.ext
      apply AffineEquiv.ext
      intro y
      obtain ⟨x,rfl⟩ := (rep g).2 y
      exact congrArg (fun a : SurjectiveAffineMaps V W => a.1 x) h
    · intro b
      let g : affinePullbackFamily V f := ⟨(fun x => f (b.1 x)),⟨b,rfl⟩⟩
      obtain ⟨e,he,_⟩ := existsUnique_stabilizer_of_pullback_eq f hf (rep g).1 b.1 (rep g).2 b.2 (hrep g)
      refine ⟨(g,e),?_⟩
      apply Subtype.ext
      apply AffineMap.ext
      exact he
  rw [←Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective Ψ hbij)
/-- Surjective affine maps are exactly a translation and a surjective linear map. -/
def surjectiveAffineMapCoordinates : SurjectiveAffineMaps V W ≃
    W × {L : V →ₗ[ZMod 2] W // Function.Surjective L} :=
  { toFun := fun a => (a.1 0,⟨a.1.linear,a.1.linear_surjective_iff.mpr a.2⟩)
    invFun := fun p =>
      ⟨p.2.1.toAffineMap+AffineMap.const (ZMod 2) V p.1,by
        intro y
        obtain ⟨x,hx⟩ := p.2.2 (y-p.1)
        exact ⟨x,by simpa using congrArg (fun w => w+p.1) hx⟩⟩
    left_inv := by
      intro a
      apply Subtype.ext
      apply AffineMap.ext
      intro x
      simpa using (a.1.map_vadd (0:V) x).symm
    right_inv := by
      intro p
      apply Prod.ext
      · simp
      · apply Subtype.ext
        ext x
        simp }
/-- Exact translation factor in the affine-surjection population. -/
theorem surjectiveAffineMaps_card : Nat.card (SurjectiveAffineMaps V W)=
    Nat.card W*Nat.card {L : V →ₗ[ZMod 2] W // Function.Surjective L} := by
  rw [Nat.card_congr surjectiveAffineMapCoordinates,Nat.card_prod]
end BinaryFieldCounterexamples.Trees
