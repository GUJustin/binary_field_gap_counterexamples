/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.BranchRecovery
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
/-!
# Descent of Boolean functions through period quotients

Definition 6.2 and the quotient clause of Lemma 6.4 (Section 6.2 of the paper)
use the literal function induced on `U / P`, where every vector of `P` is a
translation period. This module constructs that function and proves that
surjective affine template representations descend and ascend through `P`.
The intrinsic-tree version is assembled after the intrinsic/template bridge.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The Boolean function induced on a quotient by translation periods. -/
def quotientFunction (f : V → ZMod 2) (P : Submodule (ZMod 2) V)
    (hP : P ≤ periodSubmodule f) : V ⧸ P → ZMod 2 :=
  Quotient.lift f (by
    intro x y hxy
    have hp : IsPeriod f (x-y) := hP ((Submodule.quotientRel_def P).mp hxy)
    simpa using hp y)

/-- Evaluating the induced function on the class of a vector recovers the original. -/
@[simp] theorem quotientFunction_mkQ (f : V → ZMod 2) (P : Submodule (ZMod 2) V)
    (hP : P ≤ periodSubmodule f) (x : V) : quotientFunction f P hP (P.mkQ x)=f x := by
  rfl

/-- A Boolean function constant on quotient fibers is uniquely determined by its pullback. -/
theorem quotientFunction_unique (f : V → ZMod 2) (P : Submodule (ZMod 2) V)
    (hP : P ≤ periodSubmodule f) (g : V ⧸ P → ZMod 2)
    (hg : ∀ x, g (P.mkQ x)=f x) : g=quotientFunction f P hP := by
  funext q
  obtain ⟨x,rfl⟩ := P.mkQ_surjective q
  exact hg x

/-- A surjective affine template representation exists before quotienting by periods
exactly when it exists for the induced function on the quotient. -/
theorem affinePullbackFamily_quotient_iff (n : ℕ) (f : V → ZMod 2)
    (P : Submodule (ZMod 2) V) (hP : P ≤ periodSubmodule f) :
    f ∈ affinePullbackFamily V (template n) ↔
      quotientFunction f P hP ∈ affinePullbackFamily (V ⧸ P) (template n) := by
  constructor
  · rintro ⟨⟨a,ha⟩,rfl⟩
    have hker : P ≤ a.linear.ker := by
      intro u hu
      have hp := hP hu
      change IsPeriod (fun x => template n (a x)) u at hp
      exact (template_period_iff n (a.linear u)).mp
        ((affineMap_precompose_period_iff (template n) a ha u).mp hp)

    let b : V ⧸ P →ᵃ[ZMod 2] TemplateSpace n :=
      (P.liftQ a.linear hker).toAffineMap + AffineMap.const (ZMod 2) (V ⧸ P) (a 0)
    have hb (x : V) : b (P.mkQ x)=a x := by
      simpa [b] using (a.map_vadd (0:V) x).symm
    have hbs : Function.Surjective b := by
      intro y
      obtain ⟨x,rfl⟩ := ha y
      exact ⟨P.mkQ x,hb x⟩
    refine ⟨⟨b,hbs⟩,?_⟩
    funext q
    obtain ⟨x,rfl⟩ := P.mkQ_surjective q
    change template n (b (P.mkQ x))=template n (a x)
    rw [hb]
  · rintro ⟨⟨a,ha⟩,he⟩
    refine ⟨⟨a.comp P.mkQ.toAffineMap,ha.comp P.mkQ_surjective⟩,?_⟩
    funext x
    exact (congrFun he (P.mkQ x)).trans (quotientFunction_mkQ f P hP x)

end BinaryFieldCounterexamples.Trees
