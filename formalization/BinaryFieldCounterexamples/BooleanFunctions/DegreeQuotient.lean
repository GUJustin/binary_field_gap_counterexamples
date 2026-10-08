/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.DegreeAffine
public import BinaryFieldCounterexamples.Constructions.Trees.BranchRecovery

/-!
# Degree and quotients by translation periods

The first sentence of the proof of Lemma 6.4 (tree structure, Section 6.2)
asserts that passing to a quotient by a subspace of translation periods preserves
degree. This module uses the project's `Trees.IsPeriod` and
`Trees.periodSubmodule`, defines the actual induced quotient function, and
proves that assertion by surjective linear pullback.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Evaluate at any representative of a coset. Independence of the selected
representative is proved by `periodQuotientFunction_mkQ` when `P` consists of periods. -/
def periodQuotientFunction (f : U → ZMod 2) (P : Submodule (ZMod 2) U) :
    U ⧸ P → ZMod 2 := fun q => f (Function.surjInv P.mkQ_surjective q)

/-- A period-invariant function really is the pullback of its induced quotient function. -/
theorem periodQuotientFunction_mkQ (f : U → ZMod 2) (P : Submodule (ZMod 2) U)
    (hP : P ≤ Trees.periodSubmodule f) (x : U) :
    periodQuotientFunction f P (P.mkQ x) = f x := by
  let r := Function.surjInv P.mkQ_surjective (P.mkQ x)
  have hr : P.mkQ r = P.mkQ x := Function.surjInv_eq P.mkQ_surjective _
  have hx : x - r ∈ P := (Submodule.Quotient.eq P).mp hr.symm
  have hper : Trees.IsPeriod f (x - r) := hP hx
  have h := hper r
  simpa [periodQuotientFunction, r] using h.symm

/-- The induced quotient function has exactly the original algebraic-normal-form
degree. This is the degree clause used to start the proof of Lemma 6.4. -/
theorem vectorDegree_periodQuotientFunction [FiniteDimensional (ZMod 2) U]
    (f : U → ZMod 2) (P : Submodule (ZMod 2) U) (hP : P ≤ Trees.periodSubmodule f) :
    vectorDegree (periodQuotientFunction f P) = vectorDegree f := by
  have h := vectorDegree_comp_affine_of_surjective (periodQuotientFunction f P)
    P.mkQ.toAffineMap P.mkQ_surjective
  have he : periodQuotientFunction f P ∘ P.mkQ.toAffineMap = f :=
    funext (periodQuotientFunction_mkQ f P hP)
  rw [he] at h
  exact h.symm

/-- Degree is bounded by the number of essential coordinates, measured as the
dimension of the quotient by all translation periods. -/
theorem vectorDegree_le_finrank_periodQuotient [FiniteDimensional (ZMod 2) U]
    (f : U → ZMod 2) :
    vectorDegree f ≤ Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) := by
  rw [← vectorDegree_periodQuotientFunction f (Trees.periodSubmodule f) le_rfl]
  exact vectorDegree_le_finrank _

end BinaryFieldCounterexamples.BooleanFunctions
