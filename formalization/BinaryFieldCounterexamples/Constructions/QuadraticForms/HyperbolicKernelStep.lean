/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianPascalAlternate
public import BinaryFieldCounterexamples.Counting.GaussianInversion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Gaussian inverse kernels under hyperbolic incidence extension

The literal lower Gaussian inverse turns the proved hyperbolic incidence step
into a local three-term rank recurrence. Grouping adjacent ranks gives both
requested parity recurrences. All endpoint and dimension-tail cases are
explicit. Identification with actual matrix character sums is separate.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- The literal Gaussian Möbius coefficient has its standard multiplicative step. -/
theorem gaussianMobius_succ (q a : ℕ) :
    gaussianMobius q (a+1)=-(q:ℚ)^a*gaussianMobius q a := by
  rw [gaussianMobius,gaussianMobius,←Nat.choose_two_right,←Nat.choose_two_right,
    Nat.choose_succ_succ,Nat.choose_one_right,pow_add,pow_succ]
  ring
/-- The interior inverse-incidence coefficients transform by a local three-term rank recurrence. -/
theorem hyperbolic_inverse_coefficient (q D e k : ℕ) (hq : 1<q) :
    (q:ℚ)^e*gaussianMobius q (k+2)*(gaussianPascal q (D+2) (k+2):ℚ)+
      ((q:ℚ)^(e+D+1)+(q:ℚ)^(e+1))*gaussianMobius q (k+1)*
        (gaussianPascal q (D+1) (k+1):ℚ)=
      (q:ℚ)^(e+k+2)*gaussianMobius q (k+2)*(gaussianPascal q D (k+2):ℚ)+
      ((q:ℚ)-1)*(q:ℚ)^(e+k+1)*gaussianMobius q (k+1)*(gaussianPascal q D (k+1):ℚ)-
      (q:ℚ)^(e+k+1)*gaussianMobius q k*(gaussianPascal q D k:ℚ) := by
  by_cases hk : k≤D
  · have h := gaussianPascal_succ_alt q (D+1) (k+1) hq (by omega)
    rw [show D+1-(k+1)=D-k by omega] at h
    rw [show D+2=(D+1)+1 by omega,show k+2=(k+1)+1 by omega,h,
      gaussianPascal_succ q D (k+1),gaussianPascal_succ q D k]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    have hp : (q:ℚ)^(e+D+1)=(q:ℚ)^e*(q:ℚ)^(k+1)*(q:ℚ)^(D-k) := by
      rw [←pow_add,←pow_add]; congr 1; omega
    have hp1 : (q:ℚ)^(e+k+1)=(q:ℚ)^e*(q:ℚ)^k*(q:ℚ) := by
      rw [pow_succ,pow_add]
    have hp2 : (q:ℚ)^(e+k+2)=(q:ℚ)^e*(q:ℚ)^k*(q:ℚ)^2 := by
      rw [pow_add _ (e+k) 2,pow_add]
    rw [hp,hp1,hp2,gaussianMobius_succ,gaussianMobius_succ]
    simp only [pow_succ]
    ring
  · rw [gaussianPascal_eq_zero q (D+2) (k+2) (by omega),
      gaussianPascal_eq_zero q (D+1) (k+1) (by omega),
      gaussianPascal_eq_zero q D (k+2) (by omega),
      gaussianPascal_eq_zero q D (k+1) (by omega),gaussianPascal_eq_zero q D k (by omega)]
    simp
/-- The rank-one inverse-incidence coefficient obeys the endpoint of the same recurrence. -/
theorem hyperbolic_inverse_coefficient_one (q D e : ℕ) (hq : 1<q) :
    (q:ℚ)^e*gaussianMobius q 1*(gaussianPascal q (D+2) 1:ℚ)+
      ((q:ℚ)^(e+D+1)+(q:ℚ)^(e+1))*gaussianMobius q 0*(gaussianPascal q (D+1) 0:ℚ)=
      (q:ℚ)^(e+1)*gaussianMobius q 1*(gaussianPascal q D 1:ℚ)+
      ((q:ℚ)-1)*(q:ℚ)^e*gaussianMobius q 0*(gaussianPascal q D 0:ℚ) := by
  have h := gaussianPascal_succ_alt q (D+1) 0 hq (by omega)
  rw [Nat.sub_zero] at h
  rw [show D+2=(D+1)+1 by omega,h,gaussianPascal_succ q D 0]
  simp only [gaussianPascal_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,
    gaussianMobius,pow_zero,pow_one,one_mul,mul_one]
  rw [show e+D+1=e+(D+1) by omega,pow_add,pow_succ]
  ring
/-- The literal lower-triangular Gaussian inverse kernel of an incidence sequence. -/
def rankIncidenceKernel (q d : ℕ) (a : ℕ→ℚ) (r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (r+1),gaussianMobius q (r-i)*(gaussianPascal q (d-i) (r-i):ℚ)*a i
/-- The hyperbolic incidence step expands into two finite weighted sums. -/
theorem sum_hyperbolic_incidence (q d r : ℕ) (a b w : ℕ→ℚ)
    (h0 : b 0=a 0)
    (hb : ∀ e,b (e+1)=(q:ℚ)^(e+1)*a (e+1)+((q:ℚ)^(d+1)+(q:ℚ)^(e+1))*a e) :
    (∑ i ∈ Finset.range (r+1),w i*b i)=
      (∑ i ∈ Finset.range (r+1),w i*(q:ℚ)^i*a i)+
      ∑ i ∈ Finset.range r,w (i+1)*((q:ℚ)^(d+1)+(q:ℚ)^(i+1))*a i := by
  rw [Finset.sum_range_succ' (fun i => w i*b i),
    Finset.sum_range_succ' (fun i => w i*(q:ℚ)^i*a i)]
  simp_rw [hb]
  rw [h0]
  simp only [pow_zero,mul_one]
  simp_rw [mul_add,add_mul,mul_assoc,mul_add]
  simp only [Finset.sum_add_distrib]
  abel
/-- The inverse coefficient identity in its actual shifted indices. -/
theorem hyperbolic_inverse_coefficient_shift (q d r i : ℕ) (hq : 1<q) (hi : i≤r) (hid : i≤d) :
    (q:ℚ)^i*gaussianMobius q (r+2-i)*(gaussianPascal q (d+2-i) (r+2-i):ℚ)+
      ((q:ℚ)^(d+1)+(q:ℚ)^(i+1))*gaussianMobius q (r+2-(i+1))*
        (gaussianPascal q (d+2-(i+1)) (r+2-(i+1)):ℚ)=
      (q:ℚ)^(r+2)*gaussianMobius q (r+2-i)*(gaussianPascal q (d-i) (r+2-i):ℚ)+
      ((q:ℚ)-1)*(q:ℚ)^(r+1)*gaussianMobius q (r+1-i)*(gaussianPascal q (d-i) (r+1-i):ℚ)-
      (q:ℚ)^(r+1)*gaussianMobius q (r-i)*(gaussianPascal q (d-i) (r-i):ℚ) := by
  have h := hyperbolic_inverse_coefficient q (d-i) i (r-i) hq
  simpa only [show r-i+2=r+2-i by omega,show d-i+2=d+2-i by omega,
    show i+(d-i)+1=d+1 by omega,show r-i+1=r+2-(i+1) by omega,
    show d-i+1=d+2-(i+1) by omega,show i+(r-i)+2=r+2 by omega,
    show i+(r-i)+1=r+1 by omega,show r+2-(i+1)=r+1-i by omega] using h
/-- Gaussian inversion turns the actual hyperbolic incidence step into the local raw rank-kernel recurrence. -/
theorem rankIncidenceKernel_hyperbolic (q d r : ℕ) (hq : 1<q) (a b : ℕ→ℚ)
    (ha : ∀ i, d < i → a i=0) (h0 : b 0=a 0)
    (hb : ∀ e,b (e+1)=(q:ℚ)^(e+1)*a (e+1)+((q:ℚ)^(d+1)+(q:ℚ)^(e+1))*a e) :
    rankIncidenceKernel q (d+2) b (r+2)=
      (q:ℚ)^(r+2)*rankIncidenceKernel q d a (r+2)+
      ((q:ℚ)-1)*(q:ℚ)^(r+1)*rankIncidenceKernel q d a (r+1)-
      (q:ℚ)^(r+1)*rankIncidenceKernel q d a r := by
  let w := fun D R i => gaussianMobius q (R-i)*(gaussianPascal q (D-i) (R-i):ℚ)
  have hi (i : ℕ) (hir : i≤r) :
      w (d+2) (r+2) i*(q:ℚ)^i*a i+
        w (d+2) (r+2) (i+1)*((q:ℚ)^(d+1)+(q:ℚ)^(i+1))*a i=
      (q:ℚ)^(r+2)*(w d (r+2) i*a i)+
        (((q:ℚ)-1)*(q:ℚ)^(r+1))*(w d (r+1) i*a i)-
        (q:ℚ)^(r+1)*(w d r i*a i) := by
    by_cases hid : i≤d
    · have h := congrArg (fun x : ℚ => x*a i) (hyperbolic_inverse_coefficient_shift q d r i hq hir hid)
      dsimp [w]
      linarith [h]
    · rw [ha i (by omega)]
      ring
  have hsum := Finset.sum_congr (s₁:=Finset.range (r+1)) rfl
    (fun i hi' => hi i (by have := Finset.mem_range.mp hi'; omega))
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hsum
  have hboundary :
      w (d+2) (r+2) (r+1)*(q:ℚ)^(r+1)*a (r+1)+
        w (d+2) (r+2) (r+1+1)*((q:ℚ)^(d+1)+(q:ℚ)^(r+1+1))*a (r+1)=
      (q:ℚ)^(r+2)*(w d (r+2) (r+1)*a (r+1))+
        (((q:ℚ)-1)*(q:ℚ)^(r+1))*(w d (r+1) (r+1)*a (r+1)) := by
    by_cases hid : r+1≤d
    · have h := hyperbolic_inverse_coefficient_one q (d-(r+1)) (r+1) hq
      have hd1 : d-(r+1)+2=d+2-(r+1) := by omega
      have hd2 : r+1+(d-(r+1))+1=d+1 := by omega
      simp only [hd1,hd2,show r+1+1=r+2 by omega] at h
      dsimp [w]
      simp only [show r+2-(r+1)=1 by omega,show r+2-(r+1+1)=0 by omega,Nat.sub_self,
        gaussianPascal_zero,Nat.cast_one,show r+1+1=r+2 by omega]
      have hh := congrArg (fun x : ℚ => x*a (r+1)) h
      simp only [gaussianPascal_zero,Nat.cast_one,mul_one] at hh
      linarith [hh]
    · rw [ha (r+1) (by omega)]
      ring
  have hlast : w (d+2) (r+2) (r+2)=w d (r+2) (r+2) := by simp [w,gaussianPascal_zero]
  change (∑ i ∈ Finset.range (r+2+1),w (d+2) (r+2) i*b i)=
    (q:ℚ)^(r+2)*(∑ i ∈ Finset.range (r+2+1),w d (r+2) i*a i)+
    ((q:ℚ)-1)*(q:ℚ)^(r+1)*(∑ i ∈ Finset.range (r+1+1),w d (r+1) i*a i)-
    (q:ℚ)^(r+1)*(∑ i ∈ Finset.range (r+1),w d r i*a i)
  rw [sum_hyperbolic_incidence q d (r+2) a b (w (d+2) (r+2)) h0 hb]
  simp only [show r+2=r+1+1 by omega,Finset.sum_range_succ _ (r+1+1),Finset.sum_range_succ _ (r+1)]
  have hl : w (d+2) (r+2) (r+1+1)*(q:ℚ)^(r+1+1)*a (r+1+1)=
      (q:ℚ)^(r+2)*(w d (r+2) (r+1+1)*a (r+1+1)) := by
    rw [show r+1+1=r+2 by omega,hlast]
    ring
  linarith [hsum,hboundary,hl]
/-- The rank-zero inverse kernel is the incidence value at zero. -/
theorem rankIncidenceKernel_zero (q d : ℕ) (a : ℕ→ℚ) : rankIncidenceKernel q d a 0=a 0 := by
  simp [rankIncidenceKernel,gaussianMobius,gaussianPascal_zero]
/-- The rank-one endpoint of the inverse hyperbolic recurrence. -/
theorem rankIncidenceKernel_hyperbolic_one (q d : ℕ) (hq : 1<q) (a b : ℕ→ℚ)
    (h0 : b 0=a 0)
    (hb : ∀ e,b (e+1)=(q:ℚ)^(e+1)*a (e+1)+((q:ℚ)^(d+1)+(q:ℚ)^(e+1))*a e) :
    rankIncidenceKernel q (d+2) b 1=
      (q:ℚ)*rankIncidenceKernel q d a 1+((q:ℚ)-1)*rankIncidenceKernel q d a 0 := by
  have hh := congrArg (fun x : ℚ => x*a 0) (hyperbolic_inverse_coefficient_one q d 0 hq)
  norm_num [gaussianMobius,gaussianPascal_zero] at hh
  simp only [rankIncidenceKernel,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    Nat.sub_zero,Nat.sub_self,gaussianPascal_zero,Nat.cast_one,mul_one]
  rw [h0,hb 0]
  norm_num [gaussianMobius]
  rcases hh with hh | hh
  · linarith [congrArg (fun x : ℚ => x*a 0) hh]
  · rw [hh]; ring
/-- Pair ranks 2u−1 and 2u, retaining only rank zero at u=0. -/
def groupedRankKernelA (K : ℕ→ℚ) : ℕ→ℚ
  | 0 => K 0
  | u+1 => K (2*u+1)+K (2*u+2)
/-- Pair ranks 2u and 2u+1. -/
def groupedRankKernelB (K : ℕ→ℚ) (u : ℕ) : ℚ := K (2*u)+K (2*u+1)
/-- Grouping a local raw rank recurrence gives the minus-type hyperbolic kernel step. -/
theorem groupedRankKernelA_step (q : ℕ) (K L : ℕ→ℚ)
    (h1 : L 1=(q:ℚ)*K 1+((q:ℚ)-1)*K 0)
    (hstep : ∀ r,L (r+2)=(q:ℚ)^(r+2)*K (r+2)+
      ((q:ℚ)-1)*(q:ℚ)^(r+1)*K (r+1)-(q:ℚ)^(r+1)*K r) (u : ℕ) :
    groupedRankKernelA L (u+1)=(q:ℚ)^(2*u+2)*groupedRankKernelA K (u+1)-
      (q:ℚ)^(2*u)*groupedRankKernelA K u := by
  cases u with
  | zero =>
    simp only [groupedRankKernelA,Nat.mul_zero,zero_add,pow_zero,one_mul]
    rw [h1,hstep 0]
    simp only [zero_add,pow_one]
    ring
  | succ u =>
    have hA := hstep (2*u+1)
    have hB := hstep (2*u+2)
    simp only [groupedRankKernelA]
    have hi1 : 2*(u+1)+1=2*u+1+2 := by omega
    have hi2 : 2*(u+1)+2=2*u+2+2 := by omega
    rw [hi1,hi2,hA,hB]
    simp only [show 2*u+1+2=2*u+3 by omega,show 2*u+1+1=2*u+2 by omega,
      show 2*u+2+2=2*u+4 by omega,
      show 2*(u+1)=2*u+2 by omega,pow_add]
    ring
/-- Grouping a local raw rank recurrence gives the plus-type hyperbolic kernel step. -/
theorem groupedRankKernelB_step (q : ℕ) (K L : ℕ→ℚ)
    (hstep : ∀ r,L (r+2)=(q:ℚ)^(r+2)*K (r+2)+
      ((q:ℚ)-1)*(q:ℚ)^(r+1)*K (r+1)-(q:ℚ)^(r+1)*K r) (u : ℕ) :
    groupedRankKernelB L (u+1)=(q:ℚ)^(2*u+3)*groupedRankKernelB K (u+1)-
      (q:ℚ)^(2*u+1)*groupedRankKernelB K u := by
  have hA := hstep (2*u)
  have hB := hstep (2*u+1)
  simp only [groupedRankKernelB]
  rw [show 2*(u+1)=2*u+2 by omega,show 2*u+2+1=2*u+1+2 by omega,hA,hB]
  simp only [show 2*u+1+2=2*u+3 by omega,show 2*u+1+1=2*u+2 by omega,pow_add]
  ring
/-- The plus-type zero block scales by q under the same raw endpoint recurrence. -/
theorem groupedRankKernelB_zero (q : ℕ) (K L : ℕ→ℚ)
    (h0 : L 0=K 0) (h1 : L 1=(q:ℚ)*K 1+((q:ℚ)-1)*K 0) :
    groupedRankKernelB L 0=(q:ℚ)*groupedRankKernelB K 0 := by
  simp only [groupedRankKernelB,Nat.mul_zero,zero_add,h0,h1]
  ring
/-- A dimension-supported incidence sequence has no inverse rank coefficients beyond that dimension. -/
theorem rankIncidenceKernel_tail (q d r : ℕ) (a : ℕ→ℚ)
    (ha : ∀ i, d < i → a i=0) (hr : d<r) : rankIncidenceKernel q d a r=0 := by
  unfold rankIncidenceKernel
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hid : i≤d
  · rw [gaussianPascal_eq_zero q (d-i) (r-i) (by omega)]
    simp
  · rw [ha i (by omega),mul_zero]
end BinaryFieldCounterexamples.QuadraticGeometry
