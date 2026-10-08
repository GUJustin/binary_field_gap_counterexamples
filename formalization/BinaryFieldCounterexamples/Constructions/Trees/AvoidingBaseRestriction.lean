/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Templates
/-!
# Binary tree frame restrictions

Restriction of the quadratic base template to a prescribed binary subspace.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
/-- A product of two binary linear functionals can be linear only when one factor is zero or the factors agree. -/
theorem product_linear_binary_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b : Module.Dual (ZMod 2) V) :
    (∃ c : Module.Dual (ZMod 2) V, ∀ x, a x*b x=c x) ↔ a=0 ∨ b=0 ∨ a=b := by
  constructor
  · rintro ⟨c,hc⟩
    by_cases ha : a=0
    · exact Or.inl ha
    by_cases hb : b=0
    · exact Or.inr (Or.inl hb)
    have hp (x y : V) : a x*b y+a y*b x=0 := by
      have h := hc (x+y)
      simp only [map_add] at h
      rw [←hc x,←hc y] at h
      linear_combination h
    obtain ⟨u,hu⟩ : ∃u, a u≠0 := by
      by_contra h
      apply ha
      ext x
      simpa using not_exists_not.mp h x
    have hau : a u=1 := ((show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (a u)).resolve_left hu
    have hbu : b u≠0 := by
      intro hbu
      apply hb
      ext x
      simpa [hau,hbu] using hp u x
    have hbu' : b u=1 := ((show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (b u)).resolve_left hbu
    refine Or.inr (Or.inr ?_)
    ext x
    have h : b x+a x=0 := by simpa [hau,hbu'] using hp u x
    exact (CharTwo.add_eq_zero.mp h).symm
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,by simp⟩
    · exact ⟨0,by simp⟩
    · refine ⟨a,?_⟩
      intro x
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (a x) with h|h <;> simp [h]
/-- Vanishing of a quadratic binary refinement is exactly the three degenerate restriction cases. -/
theorem quadratic_zero_restriction_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b c : Module.Dual (ZMod 2) V) :
    (∀ x, a x*b x+c x=0) ↔
      (a=0 ∧ c=0) ∨ (b=0 ∧ c=0) ∨ (a=b ∧ c=a) := by
  constructor
  · intro h
    have hc (x : V) : a x*b x=c x := CharTwo.add_eq_zero.mp (h x)
    rcases (product_linear_binary_iff a b).mp ⟨c,hc⟩ with ha|hb|hab
    · refine Or.inl ⟨ha,?_⟩
      ext x
      simpa [ha] using (hc x).symm
    · refine Or.inr (Or.inl ⟨hb,?_⟩)
      ext x
      simpa [hb] using (hc x).symm
    · refine Or.inr (Or.inr ⟨hab,?_⟩)
      ext x
      rw [←hc x,←hab]
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (a x) with h|h <;> simp [h]
  · rintro (⟨ha,hc⟩|⟨hb,hc⟩|⟨hab,hca⟩) x
    · simp [ha,hc]
    · simp [hb,hc]
    · rw [←hab,hca]
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (a x) with h|h <;>
        simp [h,show (1:ZMod 2)+1=0 by decide]
end BinaryFieldCounterexamples.Trees
