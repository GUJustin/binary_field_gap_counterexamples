/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.QuadraticRankOneWeight
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicKernelStep
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
set_option maxHeartbeats 4000000
/-- Weighted summation of the alternate Gaussian Pascal rule, with both endpoints kept. -/
theorem gaussianPascal_weighted_alternate (q r : ℕ) (hq : 1<q) (w : ℕ→ℚ) :
    (∑ e ∈ Finset.range (r+2),w e*(gaussianPascal q (r+1) e:ℚ))=
      (∑ e ∈ Finset.range (r+1),w e*(gaussianPascal q r e:ℚ))+
      ∑ e ∈ Finset.range (r+1),w (e+1)*(q:ℚ)^(r-e)*(gaussianPascal q r e:ℚ) := by
  rw [show r+2=(r+1)+1 by omega,Finset.sum_range_succ']
  have hs : (∑ e ∈ Finset.range (r+1),w (e+1)*(gaussianPascal q (r+1) (e+1):ℚ))=
      (∑ e ∈ Finset.range (r+1),w (e+1)*(gaussianPascal q r (e+1):ℚ))+
      ∑ e ∈ Finset.range (r+1),w (e+1)*(q:ℚ)^(r-e)*(gaussianPascal q r e:ℚ) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    rw [gaussianPascal_succ_alt q r e hq (by have := Finset.mem_range.mp he; omega)]
    push_cast
    ring
  rw [hs]
  have hs' : (∑ e ∈ Finset.range (r+1),w (e+1)*(gaussianPascal q r (e+1):ℚ))+w 0=
      ∑ e ∈ Finset.range (r+1),w e*(gaussianPascal q r e:ℚ) := by
    have h1 := Finset.sum_range_succ' (fun e => w e*(gaussianPascal q r e:ℚ)) (r+1)
    rw [Finset.sum_range_succ] at h1
    simp only [gaussianPascal_eq_zero q r (r+1) (by omega),Nat.cast_zero,mul_zero,add_zero,
      gaussianPascal_zero,Nat.cast_one,mul_one] at h1
    exact h1.symm
  simp only [gaussianPascal_zero,Nat.cast_one,mul_one]
  linarith
/-- The twice-shifted Möbius sum needed for an anisotropic plane. -/
def gaussianMobiusTwiceSum (q r : ℕ) : ℚ :=
  ∑ e ∈ Finset.range (r+1),gaussianMobius q (r-e)*(q:ℚ)^(2*(r-e))*
    (q:ℚ)^(e*(e+1)/2)*(gaussianPascal q r e:ℚ)
/-- The twice-shifted sum reduces to the already evaluated parity sum. -/
theorem gaussianMobiusTwiceSum_relation (q r : ℕ) (hq : 1<q) :
    (q:ℚ)*gaussianMobiusTwiceSum q r=
      (q:ℚ)^(r+1)*gaussianMobiusParitySum q r-gaussianMobiusParitySum q (r+1) := by
  have hs := gaussianPascal_weighted_alternate q r hq
    (fun e => gaussianMobius q (r+1-e)*(q:ℚ)^(r+1-e)*(q:ℚ)^(e*(e+1)/2))
  have hfirst : (∑ e ∈ Finset.range (r+1),gaussianMobius q (r+1-e)*(q:ℚ)^(r+1-e)*
      (q:ℚ)^(e*(e+1)/2)*(gaussianPascal q r e:ℚ))= -(q:ℚ)*gaussianMobiusTwiceSum q r := by
    unfold gaussianMobiusTwiceSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have her : e≤r := by have := Finset.mem_range.mp he; omega
    rw [show r+1-e=(r-e)+1 by omega,QuadraticGeometry.gaussianMobius_succ,pow_succ,
      show 2*(r-e)=(r-e)+(r-e) by omega,pow_add]
    ring
  have hsecond : (∑ e ∈ Finset.range (r+1),gaussianMobius q (r+1-(e+1))*(q:ℚ)^(r+1-(e+1))*
      (q:ℚ)^((e+1)*(e+1+1)/2)*(q:ℚ)^(r-e)*(gaussianPascal q r e:ℚ))=
      (q:ℚ)^(r+1)*gaussianMobiusParitySum q r := by
    unfold gaussianMobiusParitySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have her : e≤r := by have := Finset.mem_range.mp he; omega
    have ht : (e+1)*(e+1+1)/2=e*(e+1)/2+(e+1) := by
      rw [show (e+1)*(e+1+1)=e*(e+1)+(e+1)*2 by ring,Nat.add_mul_div_right]; norm_num
    rw [show r+1-(e+1)=r-e by omega,ht,pow_add]
    have hp : (q:ℚ)^(e+1)*(q:ℚ)^(r-e)=(q:ℚ)^(r+1) := by rw [←pow_add]; congr 1; omega
    rw [←hp]
    ring
  change gaussianMobiusParitySum q (r+1)=_ at hs
  rw [hfirst,hsecond] at hs
  linarith
/-- Even values of the twice-shifted sum reuse the established parity product. -/
theorem gaussianMobiusTwiceSum_even (q u : ℕ) (hq : 1<q) :
    gaussianMobiusTwiceSum q (2*u)=(q:ℚ)^(2*u)*mobiusParityProduct q u := by
  have h := gaussianMobiusTwiceSum_relation q (2*u) hq
  rw [gaussianMobiusParitySum_even q u hq,gaussianMobiusParitySum_odd q u hq,sub_zero,pow_succ] at h
  have hq0 : (q:ℚ)≠0 := by positivity
  apply mul_left_cancel₀ hq0
  calc
    _ = _ := h
    _ = _ := by ring
/-- Odd values of the twice-shifted sum reuse the established parity product. -/
theorem gaussianMobiusTwiceSum_odd (q u : ℕ) (hq : 1<q) :
    gaussianMobiusTwiceSum q (2*u+1)=
      -(q:ℚ)^(2*u+1)*((q:ℚ)^(2*u+1)-1)*mobiusParityProduct q u := by
  have h := gaussianMobiusTwiceSum_relation q (2*u+1) hq
  rw [gaussianMobiusParitySum_odd q u hq,show 2*u+1+1=2*(u+1) by omega,
    gaussianMobiusParitySum_even q (u+1) hq,mul_zero,zero_sub,mobiusParityProduct_succ] at h
  have hq0 : (q:ℚ)≠0 := by positivity
  apply mul_left_cancel₀ hq0
  calc
    _ = _ := h
    _ = _ := by rw [show 2*u+2=(2*u+1)+1 by omega,pow_succ]; ring
/-- The Gaussian flag identity remains valid when the outer requested dimension is too large. -/
theorem gaussianPascal_flag_upper (q h r e : ℕ) (hq : 1<q) (he : e≤r) :
    gaussianPascal q h e*gaussianPascal q (h-e) (r-e)=
      gaussianPascal q h r*gaussianPascal q r e := by
  by_cases hr : r≤h
  · exact (gaussianPascal_flag q h r e hq hr he).symm
  · rw [gaussianPascal_eq_zero q h r (by omega),zero_mul]
    by_cases heh : e≤h
    · rw [gaussianPascal_eq_zero q (h-e) (r-e) (by omega),mul_zero]
    · rw [gaussianPascal_eq_zero q h e (by omega),zero_mul]
/-- Two Pascal expansions and flag counting isolate the three codimension-two contributions. -/
theorem gaussianPascal_codim_two_flag (q h r e : ℕ) (hq : 1<q) (he : e≤r) :
    (gaussianPascal q (h+2-e) (r+2-e):ℚ)*(gaussianPascal q h e:ℚ)=
      (q:ℚ)^(2*(r+2-e))*(gaussianPascal q h (r+2):ℚ)*(gaussianPascal q (r+2) e:ℚ)+
      ((q:ℚ)+1)*(q:ℚ)^(r+1-e)*(gaussianPascal q h (r+1):ℚ)*(gaussianPascal q (r+1) e:ℚ)+
      (gaussianPascal q h r:ℚ)*(gaussianPascal q r e:ℚ) := by
  by_cases heh : e≤h
  · have hf (a : ℕ) (hea : e≤a) :
        (gaussianPascal q h e:ℚ)*(gaussianPascal q (h-e) (a-e):ℚ)=
          (gaussianPascal q h a:ℚ)*(gaussianPascal q a e:ℚ) := by
      exact_mod_cast gaussianPascal_flag_upper q h a e hq hea
    have h0 := hf r he
    have h1 := hf (r+1) (by omega)
    have h2 := hf (r+2) (by omega)
    have hd : h+2-e=(h-e)+1+1 := by omega
    have hr : r+2-e=(r-e)+1+1 := by omega
    rw [hd,hr,gaussianPascal,gaussianPascal,gaussianPascal]
    push_cast
    rw [show (r-e)+1=r+1-e by omega,show (r+1-e)+1=r+2-e by omega]
    rw [show 2*(r+2-e)=(r+2-e)+(r+2-e) by omega,pow_add]
    have hp : (q:ℚ)^(r+2-e)=(q:ℚ)*(q:ℚ)^(r+1-e) := by
      rw [show r+2-e=(r+1-e)+1 by omega,pow_succ]; ring
    simp only [mul_assoc]
    rw [←h0,←h1,←h2,hp]
    ring
  · have h0 := gaussianPascal_eq_zero q h e (by omega)
    have h1 := gaussianPascal_eq_zero q h r (by omega)
    have h2 := gaussianPascal_eq_zero q h (r+1) (by omega)
    have h3 := gaussianPascal_eq_zero q h (r+2) (by omega)
    simp [h0,h1,h2,h3]
/-- The last nontrivial endpoint in the two-step flag expansion. -/
theorem gaussianPascal_codim_two_flag_one (q h e : ℕ) (hq : 1<q) :
    (gaussianPascal q (h+2-e) 1:ℚ)*(gaussianPascal q h e:ℚ)=
      (q:ℚ)^2*(gaussianPascal q h (e+1):ℚ)*(gaussianPascal q (e+1) e:ℚ)+
      ((q:ℚ)+1)*(gaussianPascal q h e:ℚ) := by
  by_cases heh : e≤h
  · have hf := gaussianPascal_flag_upper q h (e+1) e hq (by omega)
    have hc : (gaussianPascal q h e:ℚ)*(gaussianPascal q (h-e) 1:ℚ)=
        (gaussianPascal q h (e+1):ℚ)*(gaussianPascal q (e+1) e:ℚ) := by
      simpa only [Nat.add_sub_cancel_left,Nat.cast_mul] using congrArg (fun n : ℕ => (n:ℚ)) hf
    rw [show h+2-e=(h-e)+1+1 by omega]
    simp only [gaussianPascal,gaussianPascal_zero,zero_add,pow_one]
    push_cast
    simp only [mul_assoc]
    rw [←hc]
    ring
  · simp [gaussianPascal_eq_zero q h e (by omega),gaussianPascal_eq_zero q h (e+1) (by omega)]
/-- The twice-shifted sum may be extended by its literal Gaussian zero tail. -/
theorem gaussianMobiusTwiceSum_extend (q r R : ℕ) (hr : r≤R) :
    gaussianMobiusTwiceSum q r=
      ∑ e ∈ Finset.range (R+1),gaussianMobius q (r-e)*(q:ℚ)^(2*(r-e))*
        (q:ℚ)^(e*(e+1)/2)*(gaussianPascal q r e:ℚ) := by
  unfold gaussianMobiusTwiceSum
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro e he hn
  have her : r<e := by simp only [Finset.mem_range] at hn; omega
  rw [gaussianPascal_eq_zero q r e her]
  simp
/-- The literal codimension-two inverse incidence kernel. -/
def anisotropicPlaneKernel (q h r : ℕ) : ℚ :=
  ∑ e ∈ Finset.range (r+1),gaussianMobius q (r-e)*
    (gaussianPascal q (h+2-e) (r-e):ℚ)*(q:ℚ)^(e*(e+1)/2)*(gaussianPascal q h e:ℚ)
/-- The codimension-two inverse kernel is a three-term combination of already evaluated parity sums. -/
theorem anisotropicPlaneKernel_three_term (q h r : ℕ) (hq : 1<q) :
    anisotropicPlaneKernel q h (r+2)=
      (gaussianPascal q h (r+2):ℚ)*gaussianMobiusTwiceSum q (r+2)-
      ((q:ℚ)+1)*(gaussianPascal q h (r+1):ℚ)*gaussianMobiusTwiceSum q (r+1)+
      (q:ℚ)*(gaussianPascal q h r:ℚ)*gaussianMobiusTwiceSum q r := by
  rw [gaussianMobiusTwiceSum_extend q (r+2) (r+2) le_rfl,
    gaussianMobiusTwiceSum_extend q (r+1) (r+2) (by omega),
    gaussianMobiusTwiceSum_extend q r (r+2) (by omega)]
  unfold anisotropicPlaneKernel
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have her : e≤r+2 := by have := Finset.mem_range.mp he; omega
  by_cases he0 : e≤r
  · have hf := gaussianPascal_codim_two_flag q h r e hq he0
    have hh := congrArg (fun x : ℚ => gaussianMobius q (r+2-e)*(q:ℚ)^(e*(e+1)/2)*x) hf
    have h1 : r+1-e=(r-e)+1 := by omega
    have h2 : r+2-e=((r-e)+1)+1 := by omega
    rw [h1,h2] at hh ⊢
    simp only [QuadraticGeometry.gaussianMobius_succ,pow_succ] at hh ⊢
    simp only [show 2*((r-e)+1)=2*(r-e)+2 by omega,
      show 2*((r-e)+1+1)=2*(r-e)+4 by omega] at hh ⊢
    simp only [pow_succ] at hh ⊢
    linear_combination hh
  · by_cases he1 : e=r+1
    · subst e
      have hf := gaussianPascal_codim_two_flag_one q h (r+1) hq
      have hh := congrArg (fun x : ℚ => -(q:ℚ)^((r+1)*(r+1+1)/2)*x) hf
      simp only [show r+2-(r+1)=1 by omega,Nat.sub_self,show r-(r+1)=0 by omega,
        pow_zero,mul_one,
        gaussianPascal_eq_zero q r (r+1) (by omega),Nat.cast_zero,mul_zero,add_zero] at ⊢
      norm_num [gaussianMobius] at ⊢
      simp only [show h+2-(r+1)=h+1-r by omega,show r+1+1=r+2 by omega] at hh
      rw [gaussianPascal_self]
      push_cast
      linear_combination hh
    · have he2 : e=r+2 := by omega
      subst e
      simp only [Nat.sub_self,show r+1-(r+2)=0 by omega,show r-(r+2)=0 by omega,
        gaussianPascal_zero,gaussianPascal_self,Nat.cast_one,pow_zero,mul_one,
        gaussianPascal_eq_zero q (r+1) (r+2) (by omega),
        gaussianPascal_eq_zero q r (r+2) (by omega),Nat.cast_zero,mul_zero,add_zero,sub_zero]
      simp [gaussianMobius,mul_comm]
end BinaryFieldCounterexamples
