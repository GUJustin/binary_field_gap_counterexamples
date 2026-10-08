/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.AnisotropicRadicalBase
public import BinaryFieldCounterexamples.Counting.SymmetricZeroKernel
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- The actual singular subspaces of a zero quadratic form are all subspaces. -/
theorem zeroForm_singular_card (Q : QuadraticForm k V) (hQ : ∀ x,Q x=0) (e : ℕ) :
    Nat.card (TotallySingularSubspaces Q e)=gaussianPascal (Fintype.card k) (Module.finrank k V) e := by
  classical
  by_cases he : e≤Module.finrank k V
  · let es : TotallySingularSubspaces Q e ≃ subspacesOfFinrank k V e := {
      toFun := fun S => ⟨S.val,S.property.1⟩
      invFun := fun S => ⟨S.val,S.property,fun x _ => hQ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr es,subspacesOfFinrank_card_eq_gaussianBinomial e he,
      gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card]
  · rw [totallySingularSubspaces_card_zero_of_finrank Q e (by omega),
      gaussianPascal_eq_zero _ _ _ (by omega)]
/-- The actual inverse kernel of a zero form equals the evaluated symmetric-matrix kernel. -/
theorem actual_zero_kernel (Q : QuadraticForm k V) (hQ : ∀ x,Q x=0) (r : ℕ) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) r=
      zeroQuadraticKernel (Fintype.card k) (Module.finrank k V) r := by
  unfold zeroQuadraticKernel
  congr 1
  funext e
  simp only [quadraticIncidenceSequence,zeroQuadraticIncidence,zeroForm_singular_card Q hQ]
/-- The actual lower zero-form weighted base has its exact Gaussian value. -/
theorem actual_zero_weightedA (Q : QuadraticForm k V) (hQ : ∀ x,Q x=0)
    (n j : ℕ) (hd : Module.finrank k V=2*n) (hj : j≤n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j
      (groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=
      (Fintype.card k:ℚ)^((2*n+1)*j)*(gaussianPascal ((Fintype.card k)^2) n j:ℚ) := by
  have he : rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)=
      zeroQuadraticKernel (Fintype.card k) (2*n) := by
    funext r
    rw [actual_zero_kernel Q hQ,hd]
  rw [he]
  exact zeroQuadraticKernel_weightedA _ n j Fintype.one_lt_card hj
/-- The actual upper zero-form weighted base has its exact Gaussian value. -/
theorem actual_zero_weightedB (Q : QuadraticForm k V) (hQ : ∀ x,Q x=0)
    (n j : ℕ) (hd : Module.finrank k V=2*n) (hj : j≤n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j
      (groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=
      (Fintype.card k:ℚ)^(2*n+(2*n-1)*j)*(gaussianPascal ((Fintype.card k)^2) n j:ℚ) := by
  have he : rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)=
      zeroQuadraticKernel (Fintype.card k) (2*n) := by
    funext r
    rw [actual_zero_kernel Q hQ,hd]
  rw [he]
  exact zeroQuadraticKernel_weightedB _ n j Fintype.one_lt_card hj
end BinaryFieldCounterexamples.QuadraticGeometry
