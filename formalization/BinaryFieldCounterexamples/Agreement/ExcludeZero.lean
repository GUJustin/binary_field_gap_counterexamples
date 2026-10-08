/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.Basic
/-!
# Excluding the zero challenge by a bound on the first input

A strict gap between the bound on the first input's agreement and the challenge
threshold excludes zero, so nonzero challenge counts lose no challenge.
-/
@[expose] public section
set_option linter.unusedSectionVars false
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.decEq Classical.propDecidable
/-- If the first input's agreement is strictly below the threshold, zero is not exceptional. -/
theorem zero_not_mem_badChallenges_of_source_gap
    {F:Type*} [Field F] [Fintype F] (D:Finset F) (K A T:ℕ) (f g:D→F)
    (hf:agreementLE D K f A) (hT:A<T):0∉badChallenges D K f g T := by
  intro hz
  obtain ⟨p,hp,hcount⟩:=(mem_badChallenges D K f g T 0).mp hz
  have hupper:=hf p hp
  simp only [zero_mul,add_zero] at hcount
  exact (not_le_of_gt hT) (hcount.trans hupper)
/-- Removing zero changes nothing when the first-input bound is below the threshold. -/
theorem nonzeroBadChallenges_eq_of_source_gap
    {F:Type*} [Field F] [Fintype F] (D:Finset F) (K A T:ℕ) (f g:D→F)
    (hf:agreementLE D K f A) (hT:A<T):
    nonzeroBadChallenges D K f g T=badChallenges D K f g T := by
  exact Finset.erase_eq_self.mpr (zero_not_mem_badChallenges_of_source_gap D K A T f g hf hT)
end BinaryFieldCounterexamples
