/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# Gaussian weighting of a rank-two Fourier recurrence

Pascal's identity transforms the rank-two update into multiplication by a
single power of the base. The boundary is treated explicitly: because natural
subtraction clips, the nominally out-of-range weighted sum keeps its last
sequence entry. An actual rank cutoff makes that boundary vanish.

The iteration theorem propagates a proved initial weighted identity along a
sequence with proved recurrence and cutoffs. It does not assume a Fourier
identity for actual tensors; that application must supply the concrete sums.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
/-- The Gaussian-weighted initial segment of a rank-class sequence. -/
def gaussianWeightedSum (q n s : ℕ) (P : ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range (s+1), (gaussianBinomial q (n-j) (s-j):ℚ)*P j
/-- Pascal's recurrence gives the difference of successive Gaussian weights. -/
theorem gaussianWeight_difference (q n s j : ℕ) (hq : 1<q) (hs : s≤n+1) (hj : j<s) :
    (gaussianBinomial q (n+1-j) (s-j):ℚ)-(gaussianBinomial q (n-j) (s-(j+1)):ℚ)=
      (q:ℚ)^(s-j)*(gaussianBinomial q (n-j) (s-j):ℚ) := by
  have htop : n+1-j=(n-j)+1 := by omega
  have hbot : s-j=(s-(j+1))+1 := by omega
  have hp := gaussianBinomial_succ q (n-j) (s-(j+1)) hq
  rw [←htop,←hbot] at hp
  have hcast := congrArg (fun x : ℕ => (x:ℚ)) hp
  push_cast at hcast
  linarith
/-- Gaussian weighting diagonalizes the rank-two character recurrence. -/
theorem gaussianWeightedSum_rank_step (q n s : ℕ) (hq : 1<q) (hs : s≤n+1)
    (P Q : ℕ → ℚ) (hzero : Q 0=P 0)
    (hstep : ∀ j, Q (j+1)=(q:ℚ)^(j+1)*P (j+1)-(q:ℚ)^j*P j) :
    gaussianWeightedSum q (n+1) s Q=(q:ℚ)^s*gaussianWeightedSum q n s P := by
  have hsplit : gaussianWeightedSum q (n+1) s Q=
      (∑ j ∈ Finset.range (s+1), (gaussianBinomial q (n+1-j) (s-j):ℚ)*(q:ℚ)^j*P j)-
      ∑ j ∈ Finset.range s, (gaussianBinomial q (n-j) (s-(j+1)):ℚ)*(q:ℚ)^j*P j := by
    unfold gaussianWeightedSum
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp only [hstep,hzero,mul_sub,Finset.sum_sub_distrib,pow_zero,mul_one,Nat.sub_zero,
      Nat.add_sub_add_right,←mul_assoc]
    ring
  rw [hsplit,Finset.sum_range_succ]
  have hinner : (∑ j ∈ Finset.range s, (gaussianBinomial q (n+1-j) (s-j):ℚ)*(q:ℚ)^j*P j)-
      (∑ j ∈ Finset.range s, (gaussianBinomial q (n-j) (s-(j+1)):ℚ)*(q:ℚ)^j*P j)=
      (q:ℚ)^s*∑ j ∈ Finset.range s, (gaussianBinomial q (n-j) (s-j):ℚ)*P j := by
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    have hw := gaussianWeight_difference q n s j hq hs hj
    have hp : (q:ℚ)^(s-j)*(q:ℚ)^j=(q:ℚ)^s := by rw [←pow_add,Nat.sub_add_cancel hj.le]
    calc
      _ = ((gaussianBinomial q (n+1-j) (s-j):ℚ)-(gaussianBinomial q (n-j) (s-(j+1)):ℚ))*(q:ℚ)^j*P j := by ring
      _ = (q:ℚ)^s*((gaussianBinomial q (n-j) (s-j):ℚ)*P j) := by rw [hw,←hp]; ring
  have hz (a : ℕ) : gaussianBinomial q a 0=1 := by simp [gaussianBinomial]
  unfold gaussianWeightedSum
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self,hz,Nat.cast_one,one_mul]
  linear_combination hinner
/-- Immediately above the nominal weight range, natural clipping keeps exactly the last sequence entry. -/
theorem gaussianWeightedSum_above (q n : ℕ) (P : ℕ → ℚ) :
    gaussianWeightedSum q n (n+1) P=P (n+1) := by
  unfold gaussianWeightedSum
  rw [Finset.sum_range_succ]
  have hz : (∑ j ∈ Finset.range (n+1), (gaussianBinomial q (n-j) (n+1-j):ℚ)*P j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj := Finset.mem_range.mp hj
    have hlt : ¬n+1-j≤n-j := by omega
    simp [gaussianBinomial,hlt]
  rw [hz]
  simp [gaussianBinomial]
/-- The top weighted transform vanishes when the old sequence has its actual rank cutoff. -/
theorem gaussianWeightedSum_rank_step_top (q n : ℕ) (hq : 1<q)
    (P Q : ℕ → ℚ) (hzero : Q 0=P 0)
    (hstep : ∀ j, Q (j+1)=(q:ℚ)^(j+1)*P (j+1)-(q:ℚ)^j*P j)
    (hcut : P (n+1)=0) : gaussianWeightedSum q (n+1) (n+1) Q=0 := by
  rw [gaussianWeightedSum_rank_step q n (n+1) hq le_rfl P Q hzero hstep,
    gaussianWeightedSum_above,hcut,mul_zero]
/-- Iterating the actual rank-two recurrence propagates a proved zero-frequency weighted identity. -/
theorem gaussianWeightedSum_iterate (q n : ℕ) (hq : 1<q) (γ : ℚ)
    (P : ℕ → ℕ → ℚ)
    (hbase : ∀ s, s≤n → gaussianWeightedSum q n s (P 0)=γ^s*(gaussianBinomial q n s:ℚ))
    (hzero : ∀ r, P (r+1) 0=P r 0)
    (hstep : ∀ r j, P (r+1) (j+1)=(q:ℚ)^(j+1)*P r (j+1)-(q:ℚ)^j*P r j)
    (hcut : ∀ r, P r (n+r+1)=0)
    (r s : ℕ) (hs : s≤n+r) :
    gaussianWeightedSum q (n+r) s (P r)=(γ*(q:ℚ)^r)^s*(gaussianBinomial q n s:ℚ) := by
  induction r generalizing s with
  | zero => simpa using hbase s (by simpa using hs)
  | succ r ih =>
    by_cases hsr : s≤n+r
    · rw [show n+(r+1)=(n+r)+1 by omega,
        gaussianWeightedSum_rank_step q (n+r) s hq (by omega) (P r) (P (r+1)) (hzero r) (hstep r),ih s hsr]
      rw [pow_succ,mul_pow,mul_pow,mul_pow]
      ring
    · have he : s=n+r+1 := by omega
      subst s
      rw [show n+(r+1)=n+r+1 by omega,
        gaussianWeightedSum_rank_step_top q (n+r) hq (P r) (P (r+1)) (hzero r) (hstep r) (hcut r)]
      have hn : ¬n+r+1≤n := by omega
      simp [gaussianBinomial,hn]
end BinaryFieldCounterexamples
