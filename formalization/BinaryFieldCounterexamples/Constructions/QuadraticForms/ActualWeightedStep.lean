/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualHyperbolicKernel
public import BinaryFieldCounterexamples.Counting.QuadraticKernelPropagation
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
/-- Every quadratic form either has an anisotropic radical quotient or an actual singular hyperbolic vector. -/
theorem anisotropic_quotient_or_hyperbolic_vector {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : QuadraticForm k V) :
    (Q.lift Q.radical le_rfl).Anisotropic ∨ ∃ x : V,Q x=0 ∧ x∉Q.polarBilin.ker := by
  classical
  by_cases hh : ∀ x,Q x=0→x∈Q.radical
  · left
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ x => exact (Submodule.Quotient.mk_eq_zero Q.radical).mpr (hh x hz)
  · push Not at hh
    obtain ⟨x,hx,hn⟩ := hh
    exact Or.inr ⟨x,hx,fun hp => hn ⟨hx,hp⟩⟩
variable {k V W : Type*} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V]
  [AddCommGroup W] [Module k W] [Fintype W]
/-- Actual lower grouped rank kernels vanish above half the even ambient dimension. -/
theorem actual_groupedKernelA_tail (Q : QuadraticForm k V) (n u : ℕ)
    (hd : Module.finrank k V=2*n) (hu : n<u) :
    groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)) u=0 := by
  cases u with
  | zero => omega
  | succ u =>
    simp only [groupedRankKernelA]
    rw [rankIncidenceKernel_tail _ _ _ _ (quadraticIncidenceSequence_tail Q) (by omega),
      rankIncidenceKernel_tail _ _ _ _ (quadraticIncidenceSequence_tail Q) (by omega)]
    norm_num
/-- Actual upper grouped rank kernels vanish above half the even ambient dimension. -/
theorem actual_groupedKernelB_tail (Q : QuadraticForm k V) (n u : ℕ)
    (hd : Module.finrank k V=2*n) (hu : n<u) :
    groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)) u=0 := by
  unfold groupedRankKernelB
  rw [rankIncidenceKernel_tail _ _ _ _ (quadraticIncidenceSequence_tail Q) (by omega),
    rankIncidenceKernel_tail _ _ _ _ (quadraticIncidenceSequence_tail Q) (by omega)]
  norm_num
/-- Actual lower weighted character kernels obey the hyperbolic multiplication rule. -/
theorem actual_weightedKernelA_step (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W) (n j : ℕ) (hj : j≤n+1)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) :
    gaussianWeightedSum ((Fintype.card k)^2) (n+1) j
      (groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k W) (quadraticIncidenceSequence R)))=
      (Fintype.card k:ℚ)^(2*j)*gaussianWeightedSum ((Fintype.card k)^2) n j
        (groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q))) := by
  exact groupedRankKernelA_weight_step _ n j Fintype.one_lt_card hj _ _
    (by rw [quadraticRankKernel_zero,quadraticRankKernel_zero])
    (quadraticRankKernel_hyperbolic_one p Q R hd hh hz)
    (quadraticRankKernel_hyperbolic p Q R hd hh hz)
/-- Actual upper weighted character kernels obey the hyperbolic multiplication rule. -/
theorem actual_weightedKernelB_step (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W) (n j : ℕ) (hj : j≤n+1)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) :
    gaussianWeightedSum ((Fintype.card k)^2) (n+1) j
      (groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k W) (quadraticIncidenceSequence R)))=
      (Fintype.card k:ℚ)^(2*j+1)*gaussianWeightedSum ((Fintype.card k)^2) n j
        (groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q))) := by
  exact groupedRankKernelB_weight_step _ n j Fintype.one_lt_card hj _ _
    (by rw [quadraticRankKernel_zero,quadraticRankKernel_zero])
    (quadraticRankKernel_hyperbolic_one p Q R hd hh hz)
    (quadraticRankKernel_hyperbolic p Q R hd hh hz)
end BinaryFieldCounterexamples.QuadraticGeometry
