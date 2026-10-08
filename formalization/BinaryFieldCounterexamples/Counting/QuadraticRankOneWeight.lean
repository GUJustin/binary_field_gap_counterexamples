/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianMobiusParity
public import BinaryFieldCounterexamples.Counting.GaussianFourierTransform
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The weighted rank-one quadratic kernel

The consecutive even and odd values of the rank-one incidence kernel cancel.
Consequently its grouped even kernel is a backward difference of the Gaussian
Newton blocks.  Abel summation and the Gaussian Newton identity then evaluate
the weighted moment exactly.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators

def backwardDifference (R : ℕ → ℚ) (u : ℕ) : ℚ :=
  if u=0 then R 0 else R u-R (u-1)

theorem sum_backwardDifference (j : ℕ) (w R : ℕ → ℚ) :
    (∑ u ∈ Finset.range (j+1), w u*backwardDifference R u)=
      (∑ u ∈ Finset.range j, (w u-w (u+1))*R u)+w j*R j := by
  induction j with
  | zero => simp [backwardDifference]
  | succ j ih =>
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [backwardDifference, Nat.succ_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]
    ring

theorem rankOneMinusWeightedSum (q n t : ℕ) (hq : 1<q)
    (ht0 : 0<t) (htn : t≤n) :
    (∑ u ∈ Finset.range (n-t+1),
      (gaussianPascal (q^2) (n-u) t : ℚ)*backwardDifference (rankOneNewtonBlock q n) u)=
      (q:ℚ)^((2*n+1)*(n-t))*(gaussianPascal (q^2) (n-1) (n-t):ℚ) := by
  let j := n-t
  let Q : ℕ := q^2
  let γ : ℚ := (q:ℚ)^(2*n-1)
  have hQ : 1<Q := one_lt_pow₀ hq (by decide)
  rw [sum_backwardDifference]
  have hwlast : gaussianPascal Q (n-j) t=1 := by
    have hn : n-j=t := by dsimp [j]; omega
    rw [hn,gaussianPascal_self]
  have hdiff (u : ℕ) (hu : u<j) :
      (gaussianPascal Q (n-u) t:ℚ)-(gaussianPascal Q (n-(u+1)) t:ℚ)=
        (Q:ℚ)^(j-u)*(gaussianPascal Q (n-u-1) (t-1):ℚ) := by
    have hnu : t≤n-u-1 := by dsimp [j] at hu; omega
    have hh := gaussianPascal_succ_alt Q (n-u-1) (t-1) hQ (by omega)
    have h1 : n-u-1+1=n-u := by omega
    have h2 : t-1+1=t := by omega
    have h3 : n-u-1-(t-1)=j-u := by dsimp [j]; omega
    rw [h1,h2,h3] at hh
    rw [show n-(u+1)=n-u-1 by omega]
    have hhc := congrArg (fun z : ℕ => (z:ℚ)) hh
    push_cast at hhc
    linarith
  have hterm (u : ℕ) (hu : u<j) :
      ((gaussianPascal Q (n-u) t:ℚ)-(gaussianPascal Q (n-(u+1)) t:ℚ))*
          rankOneNewtonBlock q n u =
        (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*
          (gaussianPascal Q j u:ℚ)*gaussianNewtonProduct Q γ u := by
    rw [hdiff u hu]
    have hflag := gaussianPascal_flag Q (n-1) j u hQ (by dsimp [j]; omega) (by omega)
    have he1 : n-u-1=n-1-u := by omega
    have he2 : j-u=(n-1-u)-(t-1) := by dsimp [j]; omega
    have hs := gaussianPascal_symm Q (n-1-u) (t-1) hQ (by omega)
    have hsym : gaussianPascal Q (n-1-u) (t-1)=gaussianPascal Q (n-1-u) (j-u) := by
      calc
        _ = gaussianPascal Q (n-1-u) (n-1-u-(t-1)) := hs
        _ = _ := by rw [←he2]
    rw [he1, hsym]
    dsimp [rankOneNewtonBlock, Q, γ]
    rw [show (q:ℚ)^(2*u)=((q^2:ℕ):ℚ)^u by push_cast; rw [pow_mul]]
    have hp : (Q:ℚ)^(j-u)*(Q:ℚ)^u=(Q:ℚ)^j := by
      rw [←pow_add,Nat.sub_add_cancel (by omega)]
    calc
      _ = ((Q:ℚ)^(j-u)*(Q:ℚ)^u) *
          ((gaussianPascal Q (n-1-u) (j-u):ℚ) *
            (gaussianPascal Q (n-1) u:ℚ)) * gaussianNewtonProduct Q γ u := by ring
      _ = (Q:ℚ)^j *
          ((gaussianPascal Q (n-1) j:ℚ) * (gaussianPascal Q j u:ℚ)) *
            gaussianNewtonProduct Q γ u := by
        rw [hp]
        rw [show (gaussianPascal Q (n-1-u) (j-u):ℚ) *
            (gaussianPascal Q (n-1) u:ℚ) =
            (gaussianPascal Q (n-1) j:ℚ) * (gaussianPascal Q j u:ℚ) by
          have hc := congrArg (fun z : ℕ => (z:ℚ)) hflag
          push_cast at hc
          linarith]
      _ = _ := by ring
  have hlast : (gaussianPascal Q (n-j) t:ℚ)*rankOneNewtonBlock q n j =
      (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*
        (gaussianPascal Q j j:ℚ)*gaussianNewtonProduct Q γ j := by
    rw [hwlast, Nat.cast_one, one_mul, gaussianPascal_self, Nat.cast_one]
    dsimp [rankOneNewtonBlock, Q, γ]
    rw [show (q:ℚ)^(2*j)=((q^2:ℕ):ℚ)^j by push_cast; rw [pow_mul]]
    ring
  calc
    (∑ u ∈ Finset.range j,
        ((gaussianPascal Q (n-u) t:ℚ)-(gaussianPascal Q (n-(u+1)) t:ℚ))*
          rankOneNewtonBlock q n u)+
        (gaussianPascal Q (n-j) t:ℚ)*rankOneNewtonBlock q n j =
      (∑ u ∈ Finset.range j,
        (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*
          (gaussianPascal Q j u:ℚ)*gaussianNewtonProduct Q γ u)+
        (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*
          (gaussianPascal Q j j:ℚ)*gaussianNewtonProduct Q γ j := by
            rw [hlast]
            congr 1
            apply Finset.sum_congr rfl
            intro u hu
            exact hterm u (Finset.mem_range.mp hu)
    _ = (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*
        (∑ u ∈ Finset.range (j+1),
          (gaussianPascal Q j u:ℚ)*gaussianNewtonProduct Q γ u) := by
            rw [Finset.sum_range_succ]
            rw [mul_add]
            rw [Finset.mul_sum]
            ring
    _ = (Q:ℚ)^j*(gaussianPascal Q (n-1) j:ℚ)*γ^j := by
      rw [gaussianPascal_newton]
    _ = (q:ℚ)^((2*n+1)*j)*(gaussianPascal (q^2) (n-1) j:ℚ) := by
      dsimp [Q, γ, j]
      have hcast : (((q^2:ℕ):ℚ))=(q:ℚ)^2 := by simp only [Nat.cast_pow]
      rw [hcast, ←pow_mul, ←pow_mul]
      calc
        (q:ℚ)^(2*(n-t))*(gaussianPascal (q^2) (n-1) (n-t):ℚ)*
            (q:ℚ)^((2*n-1)*(n-t)) =
          (q:ℚ)^(2*(n-t)+(2*n-1)*(n-t))*
            (gaussianPascal (q^2) (n-1) (n-t):ℚ) := by rw [pow_add]; ring
        _ = _ := by
          have hn : 0<n := by omega
          have hbase : 2+(2*n-1)=2*n+1 := by omega
          have hexp : 2*(n-t)+(2*n-1)*(n-t)=(2*n+1)*(n-t) := by
            calc
              _ = (2+(2*n-1))*(n-t) := by ring
              _ = _ := by rw [hbase]
          rw [hexp]

/-- The rank-one kernel grouped across ranks `2u-1` and `2u`. -/
noncomputable def rankOneGroupedKernelA (q n u : ℕ) : ℚ :=
  if u = 0 then rankOneIncidenceKernel q n 0
  else rankOneIncidenceKernel q n (2*u-1) + rankOneIncidenceKernel q n (2*u)

/-- The rank-one kernel grouped across ranks `2u` and `2u+1`. -/
noncomputable def rankOneGroupedKernelB (q n u : ℕ) : ℚ :=
  rankOneIncidenceKernel q n (2*u) + rankOneIncidenceKernel q n (2*u+1)

/-- The first grouped rank-one kernel is the backward difference of its Newton block. -/
theorem rankOneGroupedKernelA_eq (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n-1) :
    rankOneGroupedKernelA q n u = backwardDifference (rankOneNewtonBlock q n) u := by
  cases u with
  | zero =>
      simp [rankOneGroupedKernelA, backwardDifference,
        rankOneIncidenceKernel_even q n 0 hq hu]
  | succ u =>
      rw [rankOneGroupedKernelA, ite_eq_right (by omega), backwardDifference,
        ite_eq_right (by omega)]
      rw [show 2*(u+1)-1=2*u+1 by omega,
        rankOneIncidenceKernel_odd q n u hq (by omega),
        rankOneIncidenceKernel_even q n (u+1) hq hu]
      simp only [Nat.add_sub_cancel]
      ring

/-- The second grouped rank-one kernel vanishes identically in its valid range. -/
theorem rankOneGroupedKernelB_eq_zero (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n-1) :
    rankOneGroupedKernelB q n u = 0 := by
  rw [rankOneGroupedKernelB, rankOneIncidenceKernel_even q n u hq hu,
    rankOneIncidenceKernel_odd q n u hq hu]
  ring

/-- Exact weighted evaluation of the nonzero grouped rank-one kernel. -/
theorem rankOneGroupedKernel_weightedSum (q n t : ℕ) (hq : 1 < q)
    (ht0 : 0 < t) (htn : t ≤ n) :
    (∑ u ∈ Finset.range (n-t+1),
      (gaussianPascal (q^2) (n-u) t : ℚ) * rankOneGroupedKernelA q n u) =
      (q : ℚ)^((2*n+1)*(n-t)) *
        (gaussianPascal (q^2) (n-1) (n-t) : ℚ) := by
  rw [← rankOneMinusWeightedSum q n t hq ht0 htn]
  apply Finset.sum_congr rfl
  intro u hu
  rw [rankOneGroupedKernelA_eq q n u hq (by
    have hut : u < n-t+1 := Finset.mem_range.mp hu
    omega)]

end BinaryFieldCounterexamples
