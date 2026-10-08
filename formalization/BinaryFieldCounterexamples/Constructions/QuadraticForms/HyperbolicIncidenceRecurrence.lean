/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularClosedCounts
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularRadicalConvolution
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
# Hyperbolic incidence recurrence through exact singular counts

The common normalized polar Gaussian count satisfies the hyperbolic extension
recurrence. The exact radical convolution preserves that recurrence, including
all zero tails. Its actual-count bridge identifies this scalar convolution
with the already proved finite singular-subspace count. Gaussian inversion
into rank-character kernels is a separate subsequent step.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- The common positive factor in all normalized polar-space counts. -/
def polarPlusProduct (q m e : ℕ) : ℚ := ∏ i ∈ Finset.range e,((q:ℚ)^(m-i)+1)
/-- The common Gaussian form of all three radical-free singular counts. -/
def polarGaussianCount (q n m e : ℕ) : ℚ := (gaussianPascal q n e:ℚ)*polarPlusProduct q m e
/-- Advancing both factor parameters exposes the first positive factor. -/
theorem polarPlusProduct_shift (q m e : ℕ) :
    polarPlusProduct q (m+1) (e+1)=polarPlusProduct q m e*((q:ℚ)^(m+1)+1) := by
  simp only [polarPlusProduct,Finset.prod_range_succ',Nat.add_sub_add_right,Nat.sub_zero]
/-- Adjacent Gaussian coefficients have the exact cleared ratio. -/
theorem gaussianPascal_adjacent (q n e : ℕ) (hq : 1<q) (he : e≤n) :
    (gaussianPascal q n (e+1):ℚ)*((q:ℚ)^(e+1)-1)=
      (gaussianPascal q n e:ℚ)*((q:ℚ)^(n-e)-1) := by
  by_cases hen : e=n
  · subst e
    simp [gaussianPascal_eq_zero]
  have hel : e+1≤n := by omega
  have h1 := gaussianBinomial_mul_factorial q n e hq he
  have h2 := gaussianBinomial_mul_factorial q n (e+1) hq hel
  rw [gaussianBinomial_eq_gaussianPascal q n e hq] at h1
  rw [gaussianBinomial_eq_gaussianPascal q n (e+1) hq,gaussianFactorial_succ,
    Finset.prod_range_succ] at h2
  apply mul_right_cancel₀ (gaussianFactorial_ne_zero q e hq)
  calc
    _ = (gaussianPascal q n (e+1):ℚ)*(gaussianFactorial q e*((q:ℚ)^(e+1)-1)) := by ring
    _ = _ := h2
    _ = _ := by rw [←h1]; ring
/-- The common normalized polar count obeys the hyperbolic extension recurrence. -/
theorem polarGaussianCount_hyperbolic (q n m e : ℕ) (hq : 1<q) (hnm : n≤m+1) (he : e≤n) :
    polarGaussianCount q (n+1) (m+1) (e+1)=
      (q:ℚ)^(e+1)*polarGaussianCount q n m (e+1)+
        ((q:ℚ)^(n+m-e+1)+1)*polarGaussianCount q n m e := by
  rw [polarGaussianCount,polarPlusProduct_shift,gaussianPascal_succ]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  by_cases hen : e=n
  · subst e
    simp only [gaussianPascal_eq_zero q n (n+1) (by omega),gaussianPascal_self,
      Nat.cast_zero,Nat.cast_one,mul_zero,add_zero,one_mul,polarGaussianCount,zero_mul]
    rw [show n+m-n+1=m+1 by omega]
    ring
  have hem : e≤m := by omega
  have hp : polarPlusProduct q m (e+1)=polarPlusProduct q m e*((q:ℚ)^(m-e)+1) := by
    exact Finset.prod_range_succ _ _
  have hratio := gaussianPascal_adjacent q n e hq he
  have hp1 : (q:ℚ)^(m+1)=(q:ℚ)^(m-e)*(q:ℚ)^(e+1) := by
    rw [←pow_add]; congr 1; omega
  have hp2 : (q:ℚ)^(n+m-e+1)=(q:ℚ)^(m-e)*(q:ℚ)^(e+1)*(q:ℚ)^(n-e) := by
    rw [←pow_add,←pow_add]; congr 1; omega
  simp only [polarGaussianCount,hp,hp1,hp2]
  linarith [congrArg (fun a : ℚ => a*((q:ℚ)^(m-e)*(q:ℚ)^(e+1)*polarPlusProduct q m e)) hratio]
/-- The finite Gaussian radical convolution, extended safely by the Gaussian zero tail. -/
def rationalRadicalConvolution (q h : ℕ) (f : ℕ→ℚ) (e : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (e+1),(gaussianPascal q h a:ℚ)*(q:ℚ)^((h-a)*(e-a))*f (e-a)
/-- The zero-dimensional convolution is its literal base value. -/
theorem rationalRadicalConvolution_zero (q h : ℕ) (f : ℕ→ℚ) :
    rationalRadicalConvolution q h f 0=f 0 := by
  simp [rationalRadicalConvolution,gaussianPascal_zero]
/-- Adding one radical coordinate is the exact first-order Gaussian convolution recurrence. -/
theorem rationalRadicalConvolution_succ (q h e : ℕ) (f : ℕ→ℚ) :
    rationalRadicalConvolution q (h+1) f (e+1)=
      (q:ℚ)^(e+1)*rationalRadicalConvolution q h f (e+1)+rationalRadicalConvolution q h f e := by
  unfold rationalRadicalConvolution
  rw [Finset.sum_range_succ' (fun a => (gaussianPascal q (h+1) a:ℚ)*(q:ℚ)^((h+1-a)*(e+1-a))*f (e+1-a)),
    Finset.sum_range_succ' (fun a => (gaussianPascal q h a:ℚ)*(q:ℚ)^((h-a)*(e+1-a))*f (e+1-a))]
  simp only [gaussianPascal_zero,Nat.cast_one,one_mul,Nat.sub_zero,Nat.add_sub_add_right]
  rw [mul_add ((q:ℚ)^(e+1)),Finset.mul_sum]
  have hconst : (q:ℚ)^((h+1)*(e+1))*f (e+1)=(q:ℚ)^(e+1)*((q:ℚ)^(h*(e+1))*f (e+1)) := by
    rw [←mul_assoc,←pow_add]; congr 2; ring
  rw [hconst]
  rw [add_right_comm _ ((q:ℚ)^(e+1)*((q:ℚ)^(h*(e+1))*f (e+1))),add_left_inj,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hae : a≤e := by have := Finset.mem_range.mp ha; omega
  rw [gaussianPascal_succ]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  by_cases hah : a<h
  · have hp : (q:ℚ)^(a+1)*(q:ℚ)^((h-a)*(e-a))=
        (q:ℚ)^(e+1)*(q:ℚ)^((h-(a+1))*(e-a)) := by
      rw [←pow_add,←pow_add]
      congr 1
      have hh : h-a=(h-(a+1))+1 := by omega
      rw [hh,Nat.add_mul]
      omega
    linarith [congrArg (fun x : ℚ => x*(gaussianPascal q h (a+1):ℚ)*f (e-a)) hp]
  · rw [gaussianPascal_eq_zero q h (a+1) (by omega)]
    simp
/-- With no radical, convolution is exactly its input sequence. -/
theorem rationalRadicalConvolution_radical_zero (q e : ℕ) (f : ℕ→ℚ) :
    rationalRadicalConvolution q 0 f e=f e := by
  unfold rationalRadicalConvolution
  rw [Finset.sum_eq_single 0]
  · simp [gaussianPascal_zero]
  · intro a ha hne
    rw [gaussianPascal_eq_zero q 0 a (by omega)]
    simp
  · simp
/-- The convolution has exactly the expected ambient-dimension zero tail. -/
theorem rationalRadicalConvolution_tail (q h d e : ℕ) (f : ℕ→ℚ)
    (hf : ∀ i, d < i → f i=0) (he : d+h<e) : rationalRadicalConvolution q h f e=0 := by
  unfold rationalRadicalConvolution
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hh : a≤h
  · rw [hf (e-a) (by omega),mul_zero]
  · rw [gaussianPascal_eq_zero q h a (by omega)]
    simp
/-- Gaussian radical extension preserves the scalar hyperbolic recurrence, including its zero tail. -/
theorem rationalRadicalConvolution_hyperbolic (q d h : ℕ) (f g : ℕ→ℚ)
    (hf : ∀ i, d < i → f i=0) (hzero : g 0=f 0)
    (hstep : ∀ e,g (e+1)=(q:ℚ)^(e+1)*f (e+1)+((q:ℚ)^(d-e)+1)*f e) :
    ∀ e,rationalRadicalConvolution q h g (e+1)=
      (q:ℚ)^(e+1)*rationalRadicalConvolution q h f (e+1)+
        ((q:ℚ)^(d+h-e)+1)*rationalRadicalConvolution q h f e := by
  induction h with
  | zero => intro e; simpa only [rationalRadicalConvolution_radical_zero,Nat.add_zero] using hstep e
  | succ h ih =>
    intro e
    cases e with
    | zero =>
      rw [rationalRadicalConvolution_succ,rationalRadicalConvolution_succ,
        rationalRadicalConvolution_zero,rationalRadicalConvolution_zero,
        rationalRadicalConvolution_zero,hzero,ih 0,rationalRadicalConvolution_zero]
      simp only [zero_add,Nat.sub_zero,pow_one]
      rw [show d+(h+1)=d+h+1 by omega,pow_succ]
      ring
    | succ e =>
      rw [rationalRadicalConvolution_succ,rationalRadicalConvolution_succ,
        rationalRadicalConvolution_succ,ih (e+1),ih e]
      by_cases he : e<d+h
      · have hp : (q:ℚ)^(d+h-e)=(q:ℚ)^(d+h-(e+1))*(q:ℚ) := by
          rw [←pow_succ]; congr 1; omega
        rw [show d+(h+1)-(e+1)=d+h-e by omega,hp,
          show e+1+1=(e+1)+1 by rfl,pow_succ (q:ℚ) (e+1)]
        ring
      · have h1 := rationalRadicalConvolution_tail q h d (e+1) f hf (by omega)
        have h2 := rationalRadicalConvolution_tail q h d (e+1+1) f hf (by omega)
        rw [h1,h2,show d+h-e=0 by omega,show d+h-(e+1)=0 by omega,
          show d+(h+1)-(e+1)=0 by omega]
        ring
/-- The scalar polar recurrence includes every rank index by the exact Gaussian zero tails. -/
theorem polarGaussianCount_hyperbolic_all (q n m e : ℕ) (hq : 1<q) (hnm : n≤m+1) :
    polarGaussianCount q (n+1) (m+1) (e+1)=
      (q:ℚ)^(e+1)*polarGaussianCount q n m (e+1)+
        ((q:ℚ)^(n+m+1-e)+1)*polarGaussianCount q n m e := by
  by_cases he : e≤n
  · have hh := polarGaussianCount_hyperbolic q n m e hq hnm he
    simpa only [show n+m-e+1=n+m+1-e by omega] using hh
  · simp only [polarGaussianCount,
      gaussianPascal_eq_zero q (n+1) (e+1) (by omega),
      gaussianPascal_eq_zero q n (e+1) (by omega),gaussianPascal_eq_zero q n e (by omega),
      Nat.cast_zero,zero_mul,mul_zero,add_zero]
/-- The normalized polar counts with any radical obey the complete hyperbolic incidence recurrence. -/
theorem polarGaussianRadical_hyperbolic (q n m h e : ℕ) (hq : 1<q) (hnm : n≤m+1) :
    rationalRadicalConvolution q h (polarGaussianCount q (n+1) (m+1)) (e+1)=
      (q:ℚ)^(e+1)*rationalRadicalConvolution q h (polarGaussianCount q n m) (e+1)+
        ((q:ℚ)^(n+m+1+h-e)+1)*rationalRadicalConvolution q h (polarGaussianCount q n m) e := by
  apply rationalRadicalConvolution_hyperbolic q (n+m+1) h
  · intro i hi
    simp only [polarGaussianCount,gaussianPascal_eq_zero q n i (by omega),Nat.cast_zero,zero_mul]
  · simp [polarGaussianCount,polarPlusProduct,gaussianPascal_zero]
  · exact fun a => polarGaussianCount_hyperbolic_all q n m a hq hnm
/-- The scalar convolution is exactly the rational cast of the actual singular-subspace count. -/
theorem actual_singular_count_eq_rationalRadicalConvolution
    {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      rationalRadicalConvolution (Fintype.card k) (Module.finrank k Q.radical)
        (fun i => (Nat.card (TotallySingularSubspaces (Q.lift Q.radical le_rfl) i):ℚ)) e := by
  classical
  rw [totallySingularSubspaces_radical_convolution]
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  simp_rw [gaussianBinomial_eq_gaussianPascal (Fintype.card k) _ _ Fintype.one_lt_card]
  unfold rationalRadicalConvolution
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro a ha hnot
  have haa := Finset.mem_range.mp ha
  have hna : ¬a<min (Module.finrank k Q.radical) e+1 := by simpa only [Finset.mem_range] using hnot
  rw [gaussianPascal_eq_zero (Fintype.card k) (Module.finrank k Q.radical) a (by omega)]
  simp
end BinaryFieldCounterexamples.QuadraticGeometry
