/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Counts
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.PrescribedSpace
/-!
# The assembled intrinsic count statement

Lemma 6.6 of Section 6.2 is one theorem below: its Gaussian factorization,
minimal-domain initial value and recurrence, prescribed-essential-space count,
fixed-height growth, and point incidence all concern Definition 6.3's actual
functions and supports.
-/
@[expose] public section
attribute [local instance] Classical.decEq Classical.propDecidable
namespace BinaryFieldCounterexamples.Trees

/-- Lemma 6.6 in full: exact intrinsic counts, the initial value and recurrence
for `C_h`, the count at any prescribed essential dual space, the fixed-height
order of growth, and the exact half incidence at every point. -/
theorem isTreeFunction_count_full
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (n : ℕ) (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) U) :
    let h := n+2
    let t := 2^h-1
    let C := intrinsicTreeMinimalCount h
    Nat.card {φ : U → ZMod 2 // IsTreeFunction h φ}=
      treeSupportCount h (Module.finrank (ZMod 2) U) ∧
    Nat.card {φ : U → ZMod 2 // IsTreeFunction h φ}=
      gaussianBinomial 2 (Module.finrank (ZMod 2) U) t*C ∧
    intrinsicTreeMinimalCount 2=56 ∧
    (∀ j : ℕ, let r := 2^(j+2)-1
      intrinsicTreeMinimalCount (j+3)=
        (2^(2^(j+3)-1)-1)*gaussianBinomial 2 (2*r) r*2^(r^2)*
          intrinsicTreeMinimalCount (j+2)^2) ∧
    (∀ E : Submodule (ZMod 2) (Module.Dual (ZMod 2) U),
      Module.finrank (ZMod 2) E=t →
      Nat.card {φ : U → ZMod 2 // IsTreeFunction h φ ∧ essentialDualSpace φ=E}=C) ∧
    HasBinaryPowerGrowth (treeSupportCount h) t ∧
    (∀ x : U, 2*((intrinsicTreeSupportFamily U h).filter (fun S => x ∈ S)).card=
      (intrinsicTreeSupportFamily U h).card) := by
  classical
  refine ⟨isTreeFunction_count n hd,isTreeFunction_count_gaussian n hd,
    intrinsicTreeMinimalCount_two,intrinsicTreeMinimalCount_succ,?_,
    intrinsicTreeSupportCount_growth (n+2) (by omega),
    intrinsicTreeSupportFamily_point_incidence n⟩
  exact fun E hE => isTreeFunction_prescribed_essentialDualSpace_count n E hE

end BinaryFieldCounterexamples.Trees
