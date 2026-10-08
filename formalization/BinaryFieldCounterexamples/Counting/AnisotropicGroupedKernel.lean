/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.AnisotropicPlaneKernel
public import BinaryFieldCounterexamples.Counting.SymmetricZeroKernel
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicIncidenceRecurrence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
open QuadraticGeometry
set_option maxHeartbeats 4000000
/-- The anisotropic-plane inverse kernel has its literal rank-zero value. -/
theorem anisotropicPlaneKernel_zero (q h : ℕ) : anisotropicPlaneKernel q h 0=1 := by
  simp [anisotropicPlaneKernel,gaussianMobius,gaussianPascal_zero]
/-- The rank-one value of the anisotropic-plane inverse kernel. -/
theorem anisotropicPlaneKernel_one (q h : ℕ) (hq : 1<q) :
    anisotropicPlaneKernel q h 1= -(q:ℚ)^(h+1)-1 := by
  have ha := gaussianPascal_adjacent q h 0 hq (by omega)
  simp only [zero_add,gaussianPascal_zero,Nat.cast_one,one_mul,Nat.sub_zero,pow_one] at ha
  norm_num [anisotropicPlaneKernel,Finset.sum_range_succ,gaussianMobius,gaussianPascal_zero]
  have hg : (gaussianPascal q (h+2) 1:ℚ)=1+(q:ℚ)+(q:ℚ)^2*(gaussianPascal q h 1:ℚ) := by
    simp only [gaussianPascal,gaussianPascal_zero,zero_add,pow_one]
    push_cast
    ring
  rw [hg,pow_succ (q:ℚ) h]
  linear_combination -(q:ℚ)*ha
/-- Consecutive even and odd ranks form a negative backward difference of the even Gaussian blocks. -/
theorem anisotropicPlaneKernel_pair_even (q h u : ℕ) (hq : 1<q) (hu : 2*(u+1)≤h) :
    anisotropicPlaneKernel q h (2*(u+1))+anisotropicPlaneKernel q h (2*(u+1)+1)=
      -(q:ℚ)^(h+1)*((gaussianPascal q h (2*(u+1)):ℚ)*mobiusParityProduct q (u+1)-
        (gaussianPascal q h (2*u):ℚ)*mobiusParityProduct q u) := by
  rw [show 2*(u+1)=2*u+2 by omega,show 2*u+2+1=(2*u+1)+2 by omega,
    anisotropicPlaneKernel_three_term q h (2*u) hq,
    anisotropicPlaneKernel_three_term q h (2*u+1) hq]
  rw [show 2*u+2=2*(u+1) by omega,show 2*u+1+2=2*(u+1)+1 by omega,
    gaussianMobiusTwiceSum_even q (u+1) hq,gaussianMobiusTwiceSum_odd q u hq,
    gaussianMobiusTwiceSum_even q u hq,gaussianMobiusTwiceSum_odd q (u+1) hq]
  have ha := gaussianPascal_adjacent q h (2*(u+1)) hq hu
  have hb := gaussianPascal_adjacent q h (2*u) hq (by omega)
  have hp := mobiusParityProduct_succ q u
  have hpa : (q:ℚ)^(2*(u+1)+1)*(q:ℚ)^(h-2*(u+1))=(q:ℚ)^(h+1) := by
    rw [←pow_add]; congr 1; omega
  have hpb : (q:ℚ)^(2*u+1)*(q:ℚ)^(h-2*u)=(q:ℚ)^(h+1) := by
    rw [←pow_add]; congr 1; omega
  rw [show 2*(u+1)=2*u+2 by omega] at ha hpa ⊢
  calc
    _ = -(q:ℚ)^(2*u+2+1)*mobiusParityProduct q (u+1)*
          ((gaussianPascal q h (2*u+2):ℚ)+
            (gaussianPascal q h (2*u+2+1):ℚ)*((q:ℚ)^(2*u+2+1)-1))+
        (q:ℚ)^(2*u+1)*mobiusParityProduct q u*
          ((gaussianPascal q h (2*u):ℚ)+
            (gaussianPascal q h (2*u+1):ℚ)*((q:ℚ)^(2*u+1)-1)) := by
      rw [hp]
      simp only [pow_succ]
      ring
    _ = -(q:ℚ)^(2*u+2+1)*mobiusParityProduct q (u+1)*
          ((gaussianPascal q h (2*u+2):ℚ)*(q:ℚ)^(h-(2*u+2)))+
        (q:ℚ)^(2*u+1)*mobiusParityProduct q u*
          ((gaussianPascal q h (2*u):ℚ)*(q:ℚ)^(h-2*u)) := by
      rw [ha,hb]
      ring
    _ = _ := by
      calc
        _ = -((q:ℚ)^(2*u+2+1)*(q:ℚ)^(h-(2*u+2)))*
              (gaussianPascal q h (2*u+2):ℚ)*mobiusParityProduct q (u+1)+
            ((q:ℚ)^(2*u+1)*(q:ℚ)^(h-2*u))*
              (gaussianPascal q h (2*u):ℚ)*mobiusParityProduct q u := by ring
        _ = _ := by rw [hpa,hpb]; ring
/-- Pairing odd rank with the next even rank gives the same backward difference as the rank-one base. -/
theorem anisotropicPlaneKernel_pair_odd (q h u : ℕ) (hq : 1<q) :
    anisotropicPlaneKernel q h (2*u+1)+anisotropicPlaneKernel q h (2*u+2)=
      (gaussianPascal q (h+1) (2*(u+1)):ℚ)*mobiusParityProduct q (u+1)-
        (gaussianPascal q (h+1) (2*u):ℚ)*mobiusParityProduct q u := by
  cases u with
  | zero =>
    rw [show 2*0+1=1 by omega,show 2*0+2=0+2 by omega,
      anisotropicPlaneKernel_three_term q h 0 hq]
    norm_num [gaussianMobiusTwiceSum_even q 1 hq,gaussianMobiusTwiceSum_odd q 0 hq,
      gaussianMobiusTwiceSum_even q 0 hq,gaussianPascal_zero,mobiusParityProduct]
    have hg : (gaussianPascal q (h+1) 2:ℚ)=
        (gaussianPascal q h 1:ℚ)+(q:ℚ)^2*(gaussianPascal q h 2:ℚ) := by
      rw [gaussianPascal]; push_cast; rfl
    have ha := gaussianPascal_adjacent q h 0 hq (by omega)
    simp only [zero_add,gaussianPascal_zero,Nat.cast_one,one_mul,Nat.sub_zero,pow_one] at ha
    rw [anisotropicPlaneKernel_one q h hq,hg,pow_succ (q:ℚ) h]
    linear_combination (q:ℚ)*ha
  | succ u =>
    rw [show 2*(u+1)+1=(2*u+1)+2 by omega,show 2*(u+1)+2=(2*u+2)+2 by omega,
      anisotropicPlaneKernel_three_term q h (2*u+1) hq,
      anisotropicPlaneKernel_three_term q h (2*u+2) hq]
    have he1 : 2*u+1+2=2*(u+1)+1 := by omega
    have he2 : 2*u+1+1=2*(u+1) := by omega
    simp only [he1,he2,
      show 2*(u+1)+2=2*(u+2) by omega,
      gaussianMobiusTwiceSum_even q (u+1) hq,gaussianMobiusTwiceSum_odd q (u+1) hq,
      gaussianMobiusTwiceSum_even q (u+2) hq,gaussianMobiusTwiceSum_odd q u hq]
    have hg1 : gaussianPascal q (h+1) (2*(u+1))=
        gaussianPascal q h (2*u+1)+q^(2*(u+1))*gaussianPascal q h (2*(u+1)) := by
      rw [show 2*(u+1)=(2*u+1)+1 by omega,gaussianPascal]
    have hg2 : gaussianPascal q (h+1) (2*(u+1+1))=
        gaussianPascal q h (2*(u+1)+1)+q^(2*(u+1+1))*gaussianPascal q h (2*(u+1+1)) := by
      rw [show 2*(u+1+1)=(2*(u+1)+1)+1 by omega,gaussianPascal]
    rw [hg1,hg2]
    push_cast
    simp only [show u+2=u+1+1 by omega,mobiusParityProduct_succ]
    simp only [show 2*(u+1)=2*u+2 by omega,show 2*(u+1+1)=2*u+4 by omega,
      pow_succ]
    ring
/-- The symmetric-form even parity values equal the same established product. -/
theorem symmetricParitySum_even_product (q u : ℕ) (hq : 1<q) :
    symmetricParitySum q (2*u)=mobiusParityProduct q u := by
  induction u with
  | zero => simp [mobiusParityProduct]
  | succ u ih =>
    rw [show 2*(u+1)=2*u+2 by omega,symmetricParitySum_even_step q u hq,
      symmetricParitySum_odd_step q u hq,ih,mobiusParityProduct_succ]
    ring
/-- The anisotropic grouped lower kernel is exactly the rank-one Newton backward difference. -/
theorem anisotropicPlaneKernel_groupedA (q m u : ℕ) (hq : 1<q) (hu : u≤m) :
    groupedRankKernelA (anisotropicPlaneKernel q (2*m)) u=
      backwardDifference (rankOneNewtonBlock q (m+1)) u := by
  cases u with
  | zero => simp [groupedRankKernelA,anisotropicPlaneKernel_zero,backwardDifference,
      rankOneNewtonBlock,gaussianPascal_zero,gaussianNewtonProduct]
  | succ u =>
    rw [groupedRankKernelA,anisotropicPlaneKernel_pair_odd q (2*m) u hq]
    simp only [backwardDifference,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
    rw [←rankOneMobiusBlock_eq_newton q (m+1) (u+1) hq (by omega),
      ←rankOneMobiusBlock_eq_newton q (m+1) u hq (by omega)]
    simp only [rankOneMobiusBlock,show 2*(m+1)-1=2*m+1 by omega]
/-- The anisotropic grouped upper kernel is a scaled negative backward difference of the zero-form even Newton blocks. -/
theorem anisotropicPlaneKernel_groupedB (q m u : ℕ) (hq : 1<q) (hu : u≤m) :
    groupedRankKernelB (anisotropicPlaneKernel q (2*m)) u=
      -(q:ℚ)^(2*m+1)*backwardDifference (zeroEvenNewtonBlock q m) u := by
  cases u with
  | zero =>
    simp [groupedRankKernelB,anisotropicPlaneKernel_zero,anisotropicPlaneKernel_one q (2*m) hq,
      backwardDifference,zeroEvenNewtonBlock,gaussianPascal_zero,gaussianNewtonProduct]
  | succ u =>
    rw [groupedRankKernelB,anisotropicPlaneKernel_pair_even q (2*m) u hq (by omega)]
    simp only [backwardDifference,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
    rw [←zeroEvenBlock_eq_newton q m (u+1) hq hu,←zeroEvenBlock_eq_newton q m u hq (by omega)]
    simp only [zeroEvenBlock,symmetricParitySum_even_product q _ hq]
end BinaryFieldCounterexamples
