/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.SymmetricZeroKernel
public import BinaryFieldCounterexamples.Counting.QuadraticRankOneWeight
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Gaussian weighting of backward Newton differences

A summation-by-parts identity evaluates the backward difference of a scaled
Gaussian Newton block.  This is the common algebraic step in the odd-rank and
anisotropic-plane weighted character calculations.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators

noncomputable def scaledGaussianNewtonBlock (Q m : ℕ) (gamma : ℚ) (u : ℕ) : ℚ :=
  (Q : ℚ)^u * (gaussianPascal Q m u : ℚ) * gaussianNewtonProduct Q gamma u

/-- A Gaussian weight evaluates the backward difference of a scaled Newton block. -/
theorem gaussianPascal_weighted_backwardDifference (Q m j : ℕ) (gamma : ℚ)
    (hQ : 1 < Q) (hj : j ≤ m) :
    (∑ u ∈ Finset.range (j+1),
      (gaussianPascal Q (m+1-u) (m+1-j) : ℚ) *
        backwardDifference (scaledGaussianNewtonBlock Q m gamma) u) =
      (Q : ℚ)^j * (gaussianPascal Q m j : ℚ) * gamma^j := by
  let w : ℕ → ℚ := fun u => (gaussianPascal Q (m+1-u) (m+1-j) : ℚ)
  rw [sum_backwardDifference j w (scaledGaussianNewtonBlock Q m gamma)]
  have hwlast : w j=1 := by
    dsimp [w]
    rw [show m+1-j=m+1-j by rfl, gaussianPascal_self]
    norm_num
  have hdiff (u : ℕ) (hu : u<j) :
      w u-w (u+1) =
        (Q : ℚ)^(j-u)*(gaussianPascal Q (m-u) (m-j) : ℚ) := by
    have hh := gaussianPascal_succ_alt Q (m-u) (m-j) hQ (by omega)
    rw [show m-u+1=m+1-u by omega,
      show m-u-(m-j)=j-u by omega] at hh
    have hhc := congrArg (fun z : ℕ => (z : ℚ)) hh
    push_cast at hhc
    dsimp [w]
    rw [show m+1-(u+1)=m-u by omega,
      show m+1-j=(m-j)+1 by omega]
    linarith
  have hterm (u : ℕ) (hu : u<j) :
      (w u-w (u+1))*scaledGaussianNewtonBlock Q m gamma u =
        (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
          (gaussianPascal Q j u : ℚ)*gaussianNewtonProduct Q gamma u := by
    rw [hdiff u hu]
    unfold scaledGaussianNewtonBlock
    have hp : (Q : ℚ)^(j-u)*(Q : ℚ)^u=(Q : ℚ)^j := by
      rw [←pow_add, Nat.sub_add_cancel (by omega)]
    have hf := gaussianPascal_flag Q m j u hQ hj (by omega)
    have hs := gaussianPascal_symm Q (m-u) (m-j) hQ (by omega)
    rw [show m-u-(m-j)=j-u by omega] at hs
    have hfc := congrArg (fun z : ℕ => (z : ℚ)) hf
    push_cast at hfc
    calc
      _ = ((Q : ℚ)^(j-u)*(Q : ℚ)^u) *
          ((gaussianPascal Q (m-u) (m-j) : ℚ) *
            (gaussianPascal Q m u : ℚ)) * gaussianNewtonProduct Q gamma u := by ring
      _ = (Q : ℚ)^j *
          ((gaussianPascal Q m j : ℚ) * (gaussianPascal Q j u : ℚ)) *
            gaussianNewtonProduct Q gamma u := by
        rw [hp]
        rw [hs]
        rw [hfc]
        ring
      _ = _ := by ring
  have hlast : w j*scaledGaussianNewtonBlock Q m gamma j =
      (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
        (gaussianPascal Q j j : ℚ)*gaussianNewtonProduct Q gamma j := by
    rw [hwlast, gaussianPascal_self]
    unfold scaledGaussianNewtonBlock
    norm_num
  have hlast' : scaledGaussianNewtonBlock Q m gamma j =
      (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
        (gaussianPascal Q j j : ℚ)*gaussianNewtonProduct Q gamma j := by
    simpa [hwlast] using hlast
  rw [hwlast]
  simp only [one_mul]
  calc
    (∑ u ∈ Finset.range j, (w u-w (u+1))*scaledGaussianNewtonBlock Q m gamma u)+
        scaledGaussianNewtonBlock Q m gamma j =
      (∑ u ∈ Finset.range j, (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
        (gaussianPascal Q j u : ℚ)*gaussianNewtonProduct Q gamma u)+
        (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
          (gaussianPascal Q j j : ℚ)*gaussianNewtonProduct Q gamma j := by
      rw [hlast']
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      exact hterm u (Finset.mem_range.mp hu)
    _ = (Q : ℚ)^j*(gaussianPascal Q m j : ℚ)*
        (∑ u ∈ Finset.range (j+1),
          (gaussianPascal Q j u : ℚ)*gaussianNewtonProduct Q gamma u) := by
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
      ring
    _ = _ := by rw [gaussianPascal_newton]

end BinaryFieldCounterexamples
