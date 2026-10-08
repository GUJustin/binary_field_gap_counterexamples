/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingBaseCore
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingBaseFrames
public import BinaryFieldCounterexamples.Constructions.Trees.BaseLinearFrames
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
import Mathlib.Tactic.NormNum
/-!
# Actual avoiding tree families

The actual codimension-three avoiding base family has exactly the original count, obtained from the proved raw frame population and the six-element origin stabilizer.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
/-- The actual base-template linear pullback family vanishing on a prescribed subspace. -/
def baseAvoidingFamily (W : Submodule (ZMod 2) V) : Set (V → ZMod 2) :=
  constrainedLinearPullbackFamily baseTemplate (fun f => ∀ x : W, f x=0)
/-- The literal height-two avoiding family has the original exact cardinality. -/
theorem baseAvoidingFamily_card (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+3=Module.finrank (ZMod 2) V) :
    Nat.card (baseAvoidingFamily W)=avoidingTreeSupportCount 2 (Module.finrank (ZMod 2) V) := by
  have h := constrainedLinearPullbackFamily_card_mul_stabilizer baseTemplate
    baseTemplate_period_iff (fun f : V → ZMod 2 => ∀ x : W, f x=0)
  rw [baseTemplate_origin_stabilizer_card,
    Nat.card_congr (baseConstrainedFrameEquiv (fun f : V → ZMod 2 => ∀ x : W, f x=0)),
    vanishingBaseFrames_card W hW] at h
  change Nat.card (baseAvoidingFamily W)*6=168+126*(2^Module.finrank (ZMod 2) V-8) at h
  have hd : 3≤Module.finrank (ZMod 2) V := by omega
  have hp : (2:ℕ)^Module.finrank (ZMod 2) V=8*2^(Module.finrank (ZMod 2) V-3) := by
    calc
      _=2^(3+(Module.finrank (ZMod 2) V-3)) := by congr 1; omega
      _=_ := by rw [pow_add]; norm_num
  have ha : 1≤(2:ℕ)^(Module.finrank (ZMod 2) V-3) := Nat.one_le_pow _ _ (by decide)
  rw [hp] at h
  change Nat.card (baseAvoidingFamily W)=28*(6*2^(Module.finrank (ZMod 2) V-3)-5)
  omega
end BinaryFieldCounterexamples.Trees
