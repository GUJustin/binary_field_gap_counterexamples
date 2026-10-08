/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualHyperbolicIncidence
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V W : Type*} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V]
  [AddCommGroup W] [Module k W] [Fintype W]
/-- The inverse kernel of every actual quadratic form starts at one. -/
theorem quadraticRankKernel_zero (Q : QuadraticForm k V) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) 0=1 := by
  rw [rankIncidenceKernel_zero,quadraticIncidenceSequence_zero]
/-- The rank-one inverse kernel has the actual hyperbolic step. -/
theorem quadraticRankKernel_hyperbolic_one (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k W) (quadraticIncidenceSequence R) 1=
      (Fintype.card k:ℚ)*rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) 1+
        ((Fintype.card k:ℚ)-1)*rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) 0 := by
  rw [hd]
  exact rankIncidenceKernel_hyperbolic_one _ _ Fintype.one_lt_card _ _
    (by rw [quadraticIncidenceSequence_zero,quadraticIncidenceSequence_zero])
    (quadraticIncidenceSequence_hyperbolic p Q R hd hh hz)
/-- Actual quadratic forms related by a hyperbolic plane satisfy the raw rank-kernel recurrence at every rank. -/
theorem quadraticRankKernel_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) (r : ℕ) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k W) (quadraticIncidenceSequence R) (r+2)=
      (Fintype.card k:ℚ)^(r+2)*rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) (r+2)+
      ((Fintype.card k:ℚ)-1)*(Fintype.card k:ℚ)^(r+1)*rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) (r+1)-
      (Fintype.card k:ℚ)^(r+1)*rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) r := by
  rw [hd]
  exact rankIncidenceKernel_hyperbolic _ _ r Fintype.one_lt_card _ _
    (quadraticIncidenceSequence_tail Q)
    (by rw [quadraticIncidenceSequence_zero,quadraticIncidenceSequence_zero])
    (quadraticIncidenceSequence_hyperbolic p Q R hd hh hz)
end BinaryFieldCounterexamples.QuadraticGeometry
namespace BinaryFieldCounterexamples.QuadraticCoordinates
open QuadraticGeometry
variable {k : Type*} [Field k] [Fintype k]
/-- The literal character sum over symmetric matrices has the hyperbolic rank recurrence, with no assumed Fourier identity. -/
theorem rankCharacterKernel_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (d r : ℕ) (ψ : AddChar k ℂ) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d→k)) (R : QuadraticForm k (Fin (d+2)→k))
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : Fin (d+2)→k // R x=0}=(Fintype.card k-1)*(Fintype.card k)^d+
      Fintype.card k*Nat.card {x : Fin d→k // Q x=0}) :
    rankCharacterKernel (d+2) ψ R (r+2)=
      (Fintype.card k:ℂ)^(r+2)*rankCharacterKernel d ψ Q (r+2)+
      ((Fintype.card k:ℂ)-1)*(Fintype.card k:ℂ)^(r+1)*rankCharacterKernel d ψ Q (r+1)-
      (Fintype.card k:ℂ)^(r+1)*rankCharacterKernel d ψ Q r := by
  simp_rw [rankCharacterKernel_eq_inverse _ _ ψ hψ]
  have hr := quadraticRankKernel_hyperbolic p Q R (by simp) hh (by simpa using hz) r
  simp only [Module.finrank_pi,Fintype.card_fin] at hr
  exact_mod_cast hr
/-- Every actual rank-zero character sum equals one. -/
theorem rankCharacterKernel_zero (d : ℕ) (ψ : AddChar k ℂ) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d→k)) : rankCharacterKernel d ψ Q 0=1 := by
  rw [rankCharacterKernel_eq_inverse _ _ ψ hψ,rankIncidenceKernel_zero,quadraticIncidenceSequence_zero]
  norm_num
/-- The literal rank-one character sum has the boundary hyperbolic recurrence. -/
theorem rankCharacterKernel_hyperbolic_one (p : ℕ) [Fact p.Prime] [CharP k p]
    (d : ℕ) (ψ : AddChar k ℂ) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d→k)) (R : QuadraticForm k (Fin (d+2)→k))
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : Fin (d+2)→k // R x=0}=(Fintype.card k-1)*(Fintype.card k)^d+
      Fintype.card k*Nat.card {x : Fin d→k // Q x=0}) :
    rankCharacterKernel (d+2) ψ R 1=
      (Fintype.card k:ℂ)*rankCharacterKernel d ψ Q 1+
      ((Fintype.card k:ℂ)-1)*rankCharacterKernel d ψ Q 0 := by
  simp_rw [rankCharacterKernel_eq_inverse _ _ ψ hψ]
  have hr := quadraticRankKernel_hyperbolic_one p Q R (by simp) hh (by simpa using hz)
  simp only [Module.finrank_pi,Fintype.card_fin] at hr
  exact_mod_cast hr
end BinaryFieldCounterexamples.QuadraticCoordinates
