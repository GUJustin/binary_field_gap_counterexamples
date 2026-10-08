/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
/-!
# Translation of the full challenge set

In characteristic two, adding s times the second input to the first input
translates every exceptional challenge by s. The equality keeps the same threshold and
the full finite set, so it supports exact counts as well as lower bounds.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.decEq
/-- Shifting the first input translates the entire distinct challenge set. -/
theorem badChallenges_charTwo_shift
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : Finset F) (K T : ℕ) (f g : D → F) (s : F) :
    badChallenges D K (fun x=>f x+s*g x) g T =
      (badChallenges D K f g T).image (fun z=>z+s) := by
  classical
  ext z
  constructor
  · intro hz
    refine Finset.mem_image.mpr ⟨z+s,?_,by simp [add_assoc,CharTwo.add_self_eq_zero]⟩
    rw [mem_badChallenges] at hz ⊢
    have he : (fun x=>f x+(z+s)*g x)=(fun x=>(f x+s*g x)+z*g x) := by
      funext x
      ring
    rwa [he]
  · intro hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [mem_badChallenges] at hw ⊢
    have he : (fun x=>(f x+s*g x)+(w+s)*g x)=(fun x=>f x+w*g x) := by
      funext x
      rw [QuadraticConstruction.shifted_combination]
    rwa [he]
end BinaryFieldCounterexamples
