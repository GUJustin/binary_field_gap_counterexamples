/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Exact solution of the alternating-rank counting recurrence

The append-coordinate recurrence is solved in both parities using the proved
Gaussian identities. The result uses the original product-defined Gaussian
coefficient and the exact parity-dependent parameter from the manuscript.
Dimension zero and ranks beyond the ambient dimension are included.

These are recurrence theorems, not yet counts of actual alternating matrices.
An application must prove the finite counting recurrence. The natural-number
version explicitly uses its rank cutoff to justify casting clipped subtraction.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
/-- Adjacent Gaussian coefficients satisfy the exact product ratio. -/
theorem gaussianPascal_ratio (q n j : ℕ) (hq : 1<q) (hj : j<n) :
    (gaussianPascal q n (j+1):ℚ)*((q:ℚ)^(j+1)-1)=
      (gaussianPascal q n j:ℚ)*((q:ℚ)^(n-j)-1) := by
  rw [gaussianPascal_eq_factorial_div q n (j+1) hq (by omega),
    gaussianPascal_eq_factorial_div q n j hq (by omega)]
  have hs : n-j=n-(j+1)+1 := by omega
  have hf := gaussianFactorial_succ q (n-(j+1))
  rw [←hs] at hf
  rw [gaussianFactorial_succ,hf]
  have hqj : (q:ℚ)^(j+1)-1≠0 := by
    exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by exact_mod_cast hq) (by omega)))
  have hqn : (q:ℚ)^(n-j)-1≠0 := by
    exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by exact_mod_cast hq) (by omega)))
  field_simp
/-- Scaling the Newton parameter by the base shifts its factors. -/
theorem gaussianNewtonProduct_scale (q : ℕ) (γ : ℚ) (j : ℕ) :
    gaussianNewtonProduct q ((q:ℚ)*γ) (j+1)=
      (q:ℚ)^j*((q:ℚ)*γ-1)*gaussianNewtonProduct q γ j := by
  simp only [gaussianNewtonProduct,Finset.prod_range_succ',pow_zero,pow_succ]
  have hp : (∏ i ∈ Finset.range j, ((q:ℚ)*γ-(q:ℚ)^i*q))=
      (q:ℚ)^j*∏ i ∈ Finset.range j, (γ-(q:ℚ)^i) := by
    calc
      _ = ∏ i ∈ Finset.range j, (q:ℚ)*(γ-(q:ℚ)^i) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hp]
  ring
/-- The even-to-odd rank product step, expressed with its unscaled parameter. -/
theorem alternatingRankProduct_odd_step (n j : ℕ) (γ : ℚ) (hγ : 2*γ=(4:ℚ)^n) :
    (gaussianPascal 4 n (j+1):ℚ)*gaussianNewtonProduct 4 (4*γ) (j+1)=
      4^(j+1)*(gaussianPascal 4 n (j+1):ℚ)*gaussianNewtonProduct 4 γ (j+1)+
      (2*γ-4^j)*(gaussianPascal 4 n j:ℚ)*gaussianNewtonProduct 4 γ j := by
  by_cases hj : j<n
  · have hr := gaussianPascal_ratio 4 n j (by decide) hj
    have hp : (4:ℚ)^j*4^(n-j)=4^n := by rw [←pow_add,Nat.add_sub_of_le hj.le]
    have hscale := gaussianNewtonProduct_scale 4 γ j
    norm_num only [Nat.cast_ofNat] at hscale hr
    rw [hscale]
    have hs : gaussianNewtonProduct 4 γ (j+1)=gaussianNewtonProduct 4 γ j*(γ-4^j) := by
      exact Finset.prod_range_succ _ _
    rw [hs]
    have hc : (gaussianPascal 4 n (j+1):ℚ)*4^j*(4^(j+1)-1)=
        (gaussianPascal 4 n j:ℚ)*(2*γ-4^j) := by
      calc
        _ = 4^j*((gaussianPascal 4 n (j+1):ℚ)*(4^(j+1)-1)) := by ring
        _ = (gaussianPascal 4 n j:ℚ)*(4^j*4^(n-j)-4^j) := by rw [hr]; ring
        _ = _ := by rw [hp,hγ]
    linear_combination gaussianNewtonProduct 4 γ j * hc
  · have hz : gaussianPascal 4 n (j+1)=0 := gaussianPascal_eq_zero 4 n (j+1) (by omega)
    rw [hz,Nat.cast_zero,mul_zero,zero_mul,zero_mul,zero_add]
    by_cases he : j=n
    · subst j; rw [hγ]; ring
    · rw [gaussianPascal_eq_zero 4 n j (by omega),Nat.cast_zero]; ring
/-- The odd-to-even rank product step is exactly Gaussian Pascal. -/
theorem alternatingRankProduct_even_step (n j : ℕ) (γ : ℚ) :
    (gaussianPascal 4 (n+1) (j+1):ℚ)*gaussianNewtonProduct 4 γ (j+1)=
      4^(j+1)*(gaussianPascal 4 n (j+1):ℚ)*gaussianNewtonProduct 4 γ (j+1)+
      (γ-4^j)*(gaussianPascal 4 n j:ℚ)*gaussianNewtonProduct 4 γ j := by
  rw [gaussianPascal_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  have hs : gaussianNewtonProduct 4 γ (j+1)=gaussianNewtonProduct 4 γ j*(γ-4^j) := Finset.prod_range_succ _ _
  rw [hs]
  norm_num
  ring
/-- The bordered-rank recurrence determines the exact counts in both parities. -/
theorem alternatingRankSequence_parity_formula (N : ℕ → ℕ → ℚ)
    (hzero : ∀ d, N d 0=1) (hbase : ∀ j, N 0 (j+1)=0)
    (hstep : ∀ d j, N (d+1) (j+1)=4^(j+1)*N d (j+1)+(2^d-4^j)*N d j) :
    ∀ n, (∀ j, N (2*n+1) j=(gaussianPascal 4 n j:ℚ)*gaussianNewtonProduct 4 (2^(2*n+1)) j) ∧
      (∀ j, N (2*n+2) j=(gaussianPascal 4 (n+1) j:ℚ)*gaussianNewtonProduct 4 (2^(2*n+1)) j) := by
  have heven (n : ℕ)
      (ho : ∀ j, N (2*n+1) j=(gaussianPascal 4 n j:ℚ)*gaussianNewtonProduct 4 (2^(2*n+1)) j) :
      ∀ j, N (2*n+2) j=(gaussianPascal 4 (n+1) j:ℚ)*gaussianNewtonProduct 4 (2^(2*n+1)) j := by
    intro j
    cases j with
    | zero => simp [hzero,gaussianPascal_zero,gaussianNewtonProduct]
    | succ j =>
      rw [show 2*n+2=(2*n+1)+1 by omega,hstep,ho,ho]
      simpa only [mul_assoc] using (alternatingRankProduct_even_step n j (2^(2*n+1))).symm
  intro n
  induction n with
  | zero =>
    have ho : ∀ j, N 1 j=(gaussianPascal 4 0 j:ℚ)*gaussianNewtonProduct 4 2 j := by
      intro j
      cases j with
      | zero => simp [hzero,gaussianPascal_zero,gaussianNewtonProduct]
      | succ j =>
        rw [show 1=0+1 from rfl,hstep,hbase]
        cases j with
        | zero => simp [hzero,gaussianPascal]
        | succ j => simp [hbase,gaussianPascal]
    exact ⟨by simpa using ho,heven 0 (by simpa using ho)⟩
  | succ n ih =>
    have ho : ∀ j, N (2*(n+1)+1) j=(gaussianPascal 4 (n+1) j:ℚ)*gaussianNewtonProduct 4 (2^(2*(n+1)+1)) j := by
      intro j
      cases j with
      | zero => simp [hzero,gaussianPascal_zero,gaussianNewtonProduct]
      | succ j =>
        have hγ : 2*(2:ℚ)^(2*n+1)=4^(n+1) := by
          rw [show (4:ℚ)=2^2 by norm_num,←pow_mul,←pow_succ']
          congr 1
        have hpow : (2:ℚ)^(2*n+2)=2*2^(2*n+1) := by rw [pow_succ']
        have hscale : (2:ℚ)^(2*n+2+1)=4*2^(2*n+1) := by
          rw [show 2*n+2+1=(2*n+1)+2 by omega,pow_add]
          ring
        rw [show 2*(n+1)+1=(2*n+2)+1 by omega,hstep,ih.2,ih.2,hpow,hscale]
        simpa only [mul_assoc] using (alternatingRankProduct_odd_step (n+1) j (2^(2*n+1)) hγ).symm
    exact ⟨ho,heven (n+1) ho⟩
/-- The bordered-rank recurrence gives the literal Gaussian rank product in every dimension. -/
theorem alternatingRankSequence_formula (N : ℕ → ℕ → ℚ)
    (hzero : ∀ d, N d 0=1) (hbase : ∀ j, N 0 (j+1)=0)
    (hstep : ∀ d j, N (d+1) (j+1)=4^(j+1)*N d (j+1)+(2^d-4^j)*N d j)
    (d j : ℕ) :
    N d j=(gaussianBinomial 4 (d/2) j:ℚ)*
      ∏ i ∈ Finset.range j, ((2:ℚ)^(d-(if d%2=0 then 1 else 0))-4^i) := by
  rw [gaussianBinomial_eq_gaussianPascal 4 (d/2) j (by decide)]
  have hp := alternatingRankSequence_parity_formula N hzero hbase hstep
  have hdiv := Nat.mod_add_div d 2
  rcases Nat.mod_two_eq_zero_or_one d with he | ho
  · rw [he,ite_eq_left rfl]
    by_cases hd : d=0
    · subst d
      cases j with
      | zero => simp [hzero,gaussianPascal_zero]
      | succ j => simp [hbase,gaussianPascal]
    · have hn : d=2*(d/2-1)+2 := by omega
      have hquot : d/2=(d/2-1)+1 := by omega
      have hexp : d-1=2*(d/2-1)+1 := by omega
      rw [hexp]
      conv_lhs => rw [hn]
      simpa only [←hquot,gaussianNewtonProduct,Nat.cast_ofNat] using (hp (d/2-1)).2 j
  · rw [ho,ite_eq_right (by decide : ¬1=0),Nat.sub_zero]
    have hn : d=2*(d/2)+1 := by omega
    conv_lhs => rw [hn]
    conv_rhs => arg 2; rw [hn]
    simpa only [gaussianNewtonProduct,Nat.cast_ofNat] using (hp (d/2)).1 j
/-- Natural bordered-rank counts have the exact rational product, with clipped subtraction justified by the rank cutoff. -/
theorem alternatingRankNatSequence_formula (N : ℕ → ℕ → ℕ)
    (hzero : ∀ d, N d 0=1) (hbase : ∀ j, N 0 (j+1)=0)
    (hvanish : ∀ d j, d<2*j → N d j=0)
    (hstep : ∀ d j, N (d+1) (j+1)=4^(j+1)*N d (j+1)+(2^d-4^j)*N d j)
    (d j : ℕ) :
    (N d j:ℚ)=(gaussianBinomial 4 (d/2) j:ℚ)*
      ∏ i ∈ Finset.range j, ((2:ℚ)^(d-(if d%2=0 then 1 else 0))-4^i) := by
  apply alternatingRankSequence_formula (fun d j => (N d j:ℚ))
  · intro d; rw [hzero]; rfl
  · intro j; rw [hbase]; rfl
  · intro d j
    rw [hstep,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow]
    by_cases hj : 2*j≤d
    · have hpow : (4:ℕ)^j≤2^d := by
        rw [show (4:ℕ)=2^2 from rfl,←pow_mul]
        exact Nat.pow_le_pow_right (by decide) hj
      rw [Nat.cast_sub hpow,Nat.cast_pow,Nat.cast_pow]
      norm_num
    · rw [hvanish d j (by omega),Nat.cast_zero,mul_zero,mul_zero]
      norm_num
end BinaryFieldCounterexamples
