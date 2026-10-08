/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.AnisotropicWeightedBase
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.AnisotropicRadicalBase
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- The actual rank kernel of an anisotropic plane quotient is the evaluated codimension-two kernel. -/
theorem actual_anisotropic_plane_kernel (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (h : ℕ) (hd : Module.finrank k V=h+2) (hr : Module.finrank k Q.radical=h) (r : ℕ) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) r=
      anisotropicPlaneKernel (Fintype.card k) h r := by
  rw [rankIncidenceKernel_anisotropic_quotient Q hQ,hd,hr]
  rfl
/-- The lower weighted character kernel is evaluated for every actual form with anisotropic plane quotient and even radical. -/
theorem actual_anisotropic_plane_weightedA (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (m j : ℕ) (hd : Module.finrank k V=2*m+2) (hr : Module.finrank k Q.radical=2*m)
    (hj : j≤m) :
    gaussianWeightedSum ((Fintype.card k)^2) (m+1) j
      (groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=
      (Fintype.card k:ℚ)^((2*m+3)*j)*(gaussianPascal ((Fintype.card k)^2) m j:ℚ) := by
  have he : rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)=
      anisotropicPlaneKernel (Fintype.card k) (2*m) := by
    funext r
    exact actual_anisotropic_plane_kernel Q hQ (2*m) hd hr r
  rw [he]
  exact anisotropicPlaneKernel_weightedA _ m j Fintype.one_lt_card hj
/-- The upper weighted character kernel has the actual negative anisotropic sign. -/
theorem actual_anisotropic_plane_weightedB (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (m j : ℕ) (hd : Module.finrank k V=2*m+2) (hr : Module.finrank k Q.radical=2*m)
    (hj : j≤m) :
    gaussianWeightedSum ((Fintype.card k)^2) (m+1) j
      (groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=
      -(Fintype.card k:ℚ)^((2*m+1)*(j+1))*(gaussianPascal ((Fintype.card k)^2) m j:ℚ) := by
  have he : rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)=
      anisotropicPlaneKernel (Fintype.card k) (2*m) := by
    funext r
    exact actual_anisotropic_plane_kernel Q hQ (2*m) hd hr r
  rw [he]
  exact anisotropicPlaneKernel_weightedB _ m j Fintype.one_lt_card hj
end BinaryFieldCounterexamples.QuadraticGeometry
