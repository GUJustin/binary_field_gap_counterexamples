/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.TensorBorder
/-!
# Canonical hyperbolic augmentation of alternating tensors
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Matrix
/-- Adjoin two final coordinates carrying one hyperbolic edge. -/
noncomputable def hyperbolicAugment (d : ℕ) (A : TensorIndex d → ZMod 2) :
    TensorIndex (d+2) → ZMod 2 :=
  (tensorBorderEquiv (d+1)).symm
    ((tensorBorderEquiv d).symm (A,0), Pi.single (Fin.last d) 1)

@[simp] theorem tensorBorderEquiv_hyperbolicAugment (d : ℕ)
    (A : TensorIndex d → ZMod 2) :
    tensorBorderEquiv (d+1) (hyperbolicAugment d A) =
      ((tensorBorderEquiv d).symm (A,0), Pi.single (Fin.last d) 1) := by
  rw [hyperbolicAugment, LinearEquiv.apply_symm_apply]

@[simp] theorem tensorBorderEquiv_hyperbolicAugment_old (d : ℕ)
    (A : TensorIndex d → ZMod 2) :
    tensorBorderEquiv d (tensorBorderEquiv (d+1) (hyperbolicAugment d A)).1 = (A,0) := by
  rw [tensorBorderEquiv_hyperbolicAugment, LinearEquiv.apply_symm_apply]

/-- Pairing with a hyperbolic augmentation adds the final border coordinate. -/
theorem dotProduct_hyperbolicAugment (d : ℕ)
    (B : TensorIndex (d+2) → ZMod 2) (A : TensorIndex d → ZMod 2) :
    dotProduct B (hyperbolicAugment d A) =
      dotProduct (tensorBorderEquiv d (tensorBorderEquiv (d+1) B).1).1 A +
        (tensorBorderEquiv (d+1) B).2 (Fin.last d) := by
  rw [tensorBorder_dotProduct (d+1), tensorBorderEquiv_hyperbolicAugment,
    tensorBorder_dotProduct d, LinearEquiv.apply_symm_apply]
  rw [dotProduct_single_one]
  simp [dotProduct]
end BinaryFieldCounterexamples.Gold
