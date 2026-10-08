/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.StabilizerForms
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingBaseCore
public import BinaryFieldCounterexamples.Constructions.Trees.OriginStabilizers
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateCounts
/-!
# Canonical avoiding tree support data

Actual zero-fiber transitivity propagates through branching and identifies the exact origin stabilizer as twice the manuscript denominator.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Transitivity on the zero fiber propagates through the independent branch construction. -/
theorem branch_stabilizer_zero_image {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2)
    (hf : ∀ c, f c=0 → ∃ e : affineFunctionStabilizer f, e.1 0=c)
    (c : ZMod 2 × V × V) (hc : branch f f c=0) :
    ∃ e : affineFunctionStabilizer (branch f f), e.1 0=c := by
  have hid : AffineEquiv.refl (ZMod 2) V ∈ affineFunctionStabilizer f := by
    rw [mem_affineFunctionStabilizer]
    intro x
    rfl
  rcases c with ⟨z,x,y⟩
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) z with rfl|rfl
  · have hx : f x=0 := by simpa [branch] using hc
    obtain ⟨e,he⟩ := hf x hx
    refine ⟨⟨branchForm 0 e.1 (AffineEquiv.refl (ZMod 2) V) 0 y,
      branchForm_stabilizes f 0 e.1 _ e.2 hid 0 y⟩,?_⟩
    simp [branchForm,branchPreservingForm_apply,he]
  · have hy : f y=0 := by simpa [branch] using hc
    obtain ⟨e,he⟩ := hf y hy
    refine ⟨⟨branchForm 1 e.1 (AffineEquiv.refl (ZMod 2) V) 0 x,
      branchForm_stabilizes f 1 e.1 _ e.2 hid 0 x⟩,?_⟩
    simp [branchForm,AffineEquiv.trans_apply,branchSwap_apply,branchPreservingForm_apply,he]
/-- Every actual minimal-template zero is the image of the origin under a stabilizer. -/
theorem template_stabilizer_zero_image (n : ℕ) (c : TemplateSpace n) (hc : template n c=0) :
    ∃ e : affineFunctionStabilizer (template n), e.1 0=c := by
  induction n with
  | zero => exact baseTemplate_stabilizer_zero_image c hc
  | succ n ih => exact branch_stabilizer_zero_image (template n) ih c hc
/-- Every minimal template vanishes at the actual origin. -/
theorem template_zero (n : ℕ) : template n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
/-- The actual origin stabilizer has exactly twice the manuscript denominator. -/
theorem template_origin_stabilizer_card (n : ℕ) :
    Nat.card {e : affineFunctionStabilizer (template n) // e.1 0=0}=2*treeDenominator (n+2) := by
  have h := zeroFiber_card_mul_origin_stabilizer (template n) (template_zero n)
    (template_stabilizer_zero_image n)
  rw [template_fiber_card,template_stabilizer_card] at h
  have hp : 2≤(2:ℕ)^(n+2) := by
    exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 1≤n+2)
  have he : (2:ℕ)^(2^(n+2)-1)=2^(2^(n+2)-2)*2 := by
    rw [←pow_succ]
    congr 1
    omega
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0<(2:ℕ)) (2^(n+2)-2))
  calc
    _=2^(2^(n+2)-1)*treeDenominator (n+2) := h
    _=_ := by rw [he]; ring
end BinaryFieldCounterexamples.Trees
