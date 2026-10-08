/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.AnisotropicPlaneKernel
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.AnisotropicRadicalBase
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
open QuadraticGeometry
/-- A single Pascal expansion gives the codimension-one flag coefficients at every ambient size. -/
theorem gaussianPascal_codim_one_flag (q h r e : ℕ) (hq : 1<q) (he : e≤r) :
    (gaussianPascal q (h+1-e) (r+1-e):ℚ)*(gaussianPascal q h e:ℚ)=
      (q:ℚ)^(r+1-e)*(gaussianPascal q h (r+1):ℚ)*(gaussianPascal q (r+1) e:ℚ)+
      (gaussianPascal q h r:ℚ)*(gaussianPascal q r e:ℚ) := by
  by_cases heh : e≤h
  · have hf (a : ℕ) (hea : e≤a) :
        (gaussianPascal q h e:ℚ)*(gaussianPascal q (h-e) (a-e):ℚ)=
          (gaussianPascal q h a:ℚ)*(gaussianPascal q a e:ℚ) := by
      exact_mod_cast gaussianPascal_flag_upper q h a e hq hea
    have h0 := hf r he
    have h1 := hf (r+1) (by omega)
    rw [show h+1-e=(h-e)+1 by omega,show r+1-e=(r-e)+1 by omega,gaussianPascal]
    push_cast
    rw [show r-e+1=r+1-e by omega]
    simp only [mul_assoc]
    rw [←h0,←h1]
    ring
  · simp [gaussianPascal_eq_zero q h e (by omega),gaussianPascal_eq_zero q h r (by omega),
      gaussianPascal_eq_zero q h (r+1) (by omega)]
/-- The parity sum extends by its literal Gaussian zero tail. -/
theorem gaussianMobiusParitySum_extend (q r R : ℕ) (hr : r≤R) :
    gaussianMobiusParitySum q r=
      ∑ e ∈ Finset.range (R+1),gaussianMobius q (r-e)*(q:ℚ)^(r-e)*
        (q:ℚ)^(e*(e+1)/2)*(gaussianPascal q r e:ℚ) := by
  unfold gaussianMobiusParitySum
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro e he hn
  have her : r<e := by simp only [Finset.mem_range] at hn; omega
  rw [gaussianPascal_eq_zero q r e her]
  simp
/-- The literal codimension-one inverse sum equals its two parity contributions. -/
theorem rankOne_inverse_sum_succ (q h r : ℕ) (hq : 1<q) :
    (∑ e ∈ Finset.range (r+1+1),gaussianMobius q (r+1-e)*
      (gaussianPascal q (h+1-e) (r+1-e):ℚ)*(q:ℚ)^(e*(e+1)/2)*(gaussianPascal q h e:ℚ))=
      (gaussianPascal q h (r+1):ℚ)*gaussianMobiusParitySum q (r+1)-
      (gaussianPascal q h r:ℚ)*gaussianMobiusParitySum q r := by
  rw [gaussianMobiusParitySum_extend q (r+1) (r+1) le_rfl,
    gaussianMobiusParitySum_extend q r (r+1) (by omega)]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have her : e≤r+1 := by have := Finset.mem_range.mp he; omega
  by_cases he0 : e≤r
  · have hf := gaussianPascal_codim_one_flag q h r e hq he0
    have hh := congrArg (fun x : ℚ => gaussianMobius q (r+1-e)*(q:ℚ)^(e*(e+1)/2)*x) hf
    rw [show r+1-e=(r-e)+1 by omega,gaussianMobius_succ] at hh ⊢
    linear_combination hh
  · have he1 : e=r+1 := by omega
    subst e
    simp only [Nat.sub_self,show r-(r+1)=0 by omega,gaussianPascal_zero,gaussianPascal_self,
      Nat.cast_one,pow_zero,mul_one,gaussianPascal_eq_zero q r (r+1) (by omega),
      Nat.cast_zero,mul_zero,sub_zero]
    simp [gaussianMobius,mul_comm]
/-- The actual inverse incidence kernel with codimension-one Gaussian incidence is the proved rank-one scalar kernel. -/
theorem rankOne_inverse_sum (q n r : ℕ) (hq : 1<q) (hn : 1≤n) :
    (∑ e ∈ Finset.range (r+1),gaussianMobius q (r-e)*
      (gaussianPascal q (2*n-e) (r-e):ℚ)*(q:ℚ)^(e*(e+1)/2)*(gaussianPascal q (2*n-1) e:ℚ))=
      rankOneIncidenceKernel q n r := by
  cases r with
  | zero => simp [rankOneIncidenceKernel,gaussianMobiusParityLowerSum,gaussianMobius,
      gaussianPascal_zero]
  | succ r =>
    rw [show 2*n=(2*n-1)+1 by omega,Nat.add_sub_cancel,rankOne_inverse_sum_succ q (2*n-1) r hq]
    simp only [rankOneIncidenceKernel,Nat.add_sub_cancel,gaussianMobiusParityLowerSum_succ]
    ring
namespace QuadraticGeometry
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- Every actual form with anisotropic one-dimensional radical quotient has the scalar rank-one inverse kernel. -/
theorem actual_rankOne_kernel (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (n : ℕ) (hn : 1≤n) (hd : Module.finrank k V=2*n)
    (hr : Module.finrank k Q.radical=2*n-1) (r : ℕ) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) r=
      rankOneIncidenceKernel (Fintype.card k) n r := by
  rw [rankIncidenceKernel_anisotropic_quotient Q hQ,hd,hr]
  exact rankOne_inverse_sum _ n r Fintype.one_lt_card hn
/-- The lower weighted moment of the actual rank-one base is its exact Gaussian expression. -/
theorem actual_rankOne_weightedA (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (n j : ℕ) (hn : 1≤n) (hd : Module.finrank k V=2*n)
    (hr : Module.finrank k Q.radical=2*n-1) (hj : j<n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j
      (groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=
      (Fintype.card k:ℚ)^((2*n+1)*j)*(gaussianPascal ((Fintype.card k)^2) (n-1) j:ℚ) := by
  have hq : 1<Fintype.card k := Fintype.one_lt_card
  have hQ2 : 1<(Fintype.card k)^2 := Nat.one_lt_pow (by omega) hq
  have hsum := rankOneGroupedKernel_weightedSum (Fintype.card k) n (n-j) hq (by omega) (by omega)
  rw [show n-(n-j)=j by omega] at hsum
  rw [←hsum]
  unfold gaussianWeightedSum
  apply Finset.sum_congr rfl
  intro u hu
  have huj : u≤j := by have := Finset.mem_range.mp hu; omega
  have hgroup : groupedRankKernelA (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)) u=
      rankOneGroupedKernelA (Fintype.card k) n u := by
    cases u with
    | zero => simp only [groupedRankKernelA,rankOneGroupedKernelA,↓reduceIte]; exact actual_rankOne_kernel Q hQ n hn hd hr 0
    | succ u => simp only [groupedRankKernelA,rankOneGroupedKernelA,Nat.add_eq_zero_iff,
        one_ne_zero,and_false,↓reduceIte,show 2*u+2-1=2*u+1 by omega,
        show 2*(u+1)=2*u+2 by omega,actual_rankOne_kernel Q hQ n hn hd hr]
  rw [hgroup,gaussianBinomial_eq_gaussianPascal _ _ _ hQ2]
  have hs := gaussianPascal_symm ((Fintype.card k)^2) (n-u) (j-u) hQ2 (by omega)
  rw [show n-u-(j-u)=n-j by omega] at hs
  rw [hs]
/-- The upper weighted moment of an actual rank-one base vanishes. -/
theorem actual_rankOne_weightedB (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0)
    (n j : ℕ) (hn : 1≤n) (hd : Module.finrank k V=2*n)
    (hr : Module.finrank k Q.radical=2*n-1) (hj : j<n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j
      (groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)))=0 := by
  unfold gaussianWeightedSum
  apply Finset.sum_eq_zero
  intro u hu
  have huj : u≤j := by have := Finset.mem_range.mp hu; omega
  have hgroup : groupedRankKernelB (rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)) u=
      rankOneGroupedKernelB (Fintype.card k) n u := by
    simp only [groupedRankKernelB,rankOneGroupedKernelB,actual_rankOne_kernel Q hQ n hn hd hr]
  rw [hgroup,rankOneGroupedKernelB_eq_zero _ n u Fintype.one_lt_card (by omega),mul_zero]
end QuadraticGeometry
end BinaryFieldCounterexamples
