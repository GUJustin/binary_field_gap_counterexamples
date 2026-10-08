/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Quotient
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Essential
/-!
# Essential coordinates are minimal

The gloss in Section 6.2 says a Boolean function uses its essential dual space
and no smaller space of linear tests. Here factorization through the quotient
by the common kernel of `E` is equivalent to containment of the essential
space in `E`. Thus it is a statement about actual functions, not an informal
choice of coordinates.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Section 6.2's minimality gloss: a Boolean function factors through the
linear tests in `E` exactly when `E` contains all its essential tests. -/
theorem factors_through_tests_iff (f : V → ZMod 2)
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V)) :
    (∃ g : V ⧸ E.dualCoannihilator → ZMod 2,
      ∀ x, g (E.dualCoannihilator.mkQ x) = f x) ↔ essentialDualSpace f ≤ E := by
  have he : E.dualCoannihilator ≤ periodSubmodule f ↔ essentialDualSpace f ≤ E := by
    constructor
    · intro h
      have ha := Submodule.dualAnnihilator_anti h
      simpa only [essentialDualSpace, Subspace.dualCoannihilator_dualAnnihilator_eq] using ha
    · intro h
      have ha := Submodule.dualCoannihilator_anti h
      simpa only [essentialDualSpace_dualCoannihilator] using ha
  constructor
  · rintro ⟨g,hg⟩
    apply he.mp
    intro u hu
    change ∀ x, f (x+u)=f x
    intro x
    rw [←hg (x+u),←hg x]
    congr 1
    rw [map_add]
    have hzero : E.dualCoannihilator.mkQ u = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr hu
    rw [hzero,add_zero]
  · intro h
    exact ⟨quotientFunction f E.dualCoannihilator (he.mpr h), fun x => rfl⟩

/-- Section 6.2's least-number-of-linear-tests gloss: every test space through
which the function factors has at least its essential dimension. -/
theorem essentialDimension_le_number_of_tests (f : V → ZMod 2)
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V))
    (hg : ∃ g : V ⧸ E.dualCoannihilator → ZMod 2,
      ∀ x, g (E.dualCoannihilator.mkQ x) = f x) :
    essentialDimension f ≤ finrank (ZMod 2) E := by
  exact Submodule.finrank_mono ((factors_through_tests_iff f E).mp hg)
end BinaryFieldCounterexamples.Trees
