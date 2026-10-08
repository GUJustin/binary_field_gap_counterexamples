/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
/-!
# Exact constrained linear pullback populations

Period recovery identifies equal surjective linear pullbacks up to a unique
origin-fixing affine stabilizer. The literal fiber bijection remains valid
under any property of the resulting function.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
/-- Surjective linear maps whose literal pullback satisfies a given support condition. -/
def ConstrainedSurjectiveLinearMaps (f : W → ZMod 2) (P : (V → ZMod 2) → Prop) :=
  {L : V →ₗ[ZMod 2] W // Function.Surjective L ∧ P (fun x => f (L x))}
/-- Actual distinct constrained linear pullbacks. -/
def constrainedLinearPullbackFamily (f : W → ZMod 2) (P : (V → ZMod 2) → Prop) : Set (V → ZMod 2) :=
  Set.range (fun L : ConstrainedSurjectiveLinearMaps f P => fun x => f (L.1 x))
/-- The exact origin-fixing stabilizer denominator for a constrained linear family. -/
theorem constrainedLinearPullbackFamily_card_mul_stabilizer (f : W → ZMod 2)
    (hf : ∀ u, IsPeriod f u ↔ u=0) (P : (V → ZMod 2) → Prop) :
    Nat.card (constrainedLinearPullbackFamily f P)*
      Nat.card {e : affineFunctionStabilizer f // e.1 0=0}=
      Nat.card (ConstrainedSurjectiveLinearMaps f P) := by
  classical
  let rep (g : constrainedLinearPullbackFamily f P) : ConstrainedSurjectiveLinearMaps f P :=
    Classical.choose g.property
  have hrep (g : constrainedLinearPullbackFamily f P) :
      (fun x => f ((rep g).1 x))=g.1 := Classical.choose_spec g.property
  have hlinear (e : {e : affineFunctionStabilizer f // e.1 0=0}) (x : W) :
      e.1.1.linear x=e.1.1 x := by
    have h := e.1.1.map_vadd (0:W) x
    simpa [e.2] using h.symm
  let Ψ : constrainedLinearPullbackFamily f P × {e : affineFunctionStabilizer f // e.1 0=0} →
      ConstrainedSurjectiveLinearMaps f P := fun p =>
    ⟨p.2.1.1.linear.toLinearMap.comp (rep p.1).1,
      p.2.1.1.linear.surjective.comp (rep p.1).2.1,by
        have h : (fun x => f (p.2.1.1.linear ((rep p.1).1 x)))=p.1.1 := by
          funext x
          rw [hlinear,(mem_affineFunctionStabilizer f p.2.1.1).mp p.2.1.2]
          exact congrFun (hrep p.1) x
        change P (fun x => f (p.2.1.1.linear ((rep p.1).1 x)))
        rw [h,←hrep p.1]
        exact (rep p.1).2.2⟩
  have hΨ (p : constrainedLinearPullbackFamily f P × {e : affineFunctionStabilizer f // e.1 0=0}) :
      (fun x => f ((Ψ p).1 x))=p.1.1 := by
    funext x
    change f (p.2.1.1.linear ((rep p.1).1 x))=p.1.1 x
    rw [hlinear,(mem_affineFunctionStabilizer f p.2.1.1).mp p.2.1.2]
    exact congrFun (hrep p.1) x
  have hbij : Function.Bijective Ψ := by
    constructor
    · rintro ⟨g,e⟩ ⟨g',e'⟩ h
      have hg : g=g' := by
        apply Subtype.ext
        exact (hΨ (g,e)).symm.trans ((congrArg
          (fun L : ConstrainedSurjectiveLinearMaps f P => fun x => f (L.1 x)) h).trans (hΨ (g',e')))
      subst g'
      apply congrArg (fun e => (g,e))
      apply Subtype.ext
      apply Subtype.ext
      apply AffineEquiv.ext
      intro y
      obtain ⟨x,rfl⟩ := (rep g).2.1 y
      rw [←hlinear e,←hlinear e']
      exact congrArg (fun L : ConstrainedSurjectiveLinearMaps f P => L.1 x) h
    · intro b
      let g : constrainedLinearPullbackFamily f P := ⟨(fun x => f (b.1 x)),⟨b,rfl⟩⟩
      obtain ⟨e,he,_⟩ := existsUnique_stabilizer_of_pullback_eq f hf
        (rep g).1.toAffineMap b.1.toAffineMap (rep g).2.1 b.2.1 (hrep g)
      have he0 : e.1 0=0 := by simpa using he 0
      refine ⟨(g,⟨e,he0⟩),?_⟩
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      change e.1.linear ((rep g).1 x)=b.1 x
      rw [hlinear ⟨e,he0⟩]
      exact he x
  rw [←Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective Ψ hbij)
end BinaryFieldCounterexamples.Trees
