/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianMobiusParity
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicKernelStep
public import BinaryFieldCounterexamples.Counting.GaussianFourierTransform
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# The zero-form symmetric kernel

This file evaluates both grouped inverse-incidence kernels of the zero
quadratic form on an even-dimensional space.  A reciprocal Rogers--Szegő
recurrence gives the parity factors.  Adjacent Gaussian identities identify
the grouped kernels with `q²`-Newton blocks, whose weighted transforms are
then evaluated by the Gaussian Newton formula.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators Polynomial

noncomputable def reciprocalQAlternatingSum (q n : ℕ) : ℚ :=
  Polynomial.eval (-(q : ℚ)) (reciprocalRogers q n)

noncomputable def symmetricParitySum (q r : ℕ) : ℚ :=
  ∑ e ∈ Finset.range (r+1), gaussianMobius q (r-e) *
    (q : ℚ)^(e*(e+1)/2) * gaussianPascal q r e

theorem symmetricParity_exponent (r e : ℕ) (he : e ≤ r) :
    (r-e)*(r-e-1)/2 + e*(e+1)/2 + e*(r-e) = r*(r-1)/2+e := by
  let a := r-e
  have hr : r=e+a := by dsimp [a]; omega
  rw [hr]
  have hsub : e+a-e=a := by omega
  rw [hsub]
  have h := natTriangle_add e a
  unfold natTriangle at h
  have hetri : e*(e+1)/2=e*(e-1)/2+e := by
    calc
      e*(e+1)/2 = (e+1)*((e+1)-1)/2 := by
        rw [show e+1-1=e by omega, Nat.mul_comm]
      _ = ∑ i ∈ Finset.range (e+1), i := (Finset.sum_range_id _).symm
      _ = (∑ i ∈ Finset.range e, i)+e := by rw [Finset.sum_range_succ]
      _ = _ := by rw [Finset.sum_range_id]
  rw [hetri, h]
  ring

theorem reciprocalQAlternatingSum_eq (q n : ℕ) :
    reciprocalQAlternatingSum q n =
      ∑ k ∈ Finset.range (n+1), reciprocalGaussian q n k * (-(q : ℚ))^k := by
  unfold reciprocalQAlternatingSum reciprocalRogers
  change (Polynomial.evalRingHom (-(q : ℚ)))
    (∑ k ∈ Finset.range (n+1), Polynomial.monomial k (reciprocalGaussian q n k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

theorem symmetricParitySum_eq_reciprocal (q r : ℕ) (hq : 1 < q) :
    symmetricParitySum q r =
      (-1 : ℚ)^r * (q : ℚ)^(r*(r-1)/2) * reciprocalQAlternatingSum q r := by
  rw [reciprocalQAlternatingSum_eq]
  unfold symmetricParitySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have her : e ≤ r := by simpa using Finset.mem_range.mp he
  rw [gaussianMobius, reciprocalGaussian]
  have hqn : (q : ℚ) ≠ 0 := by positivity
  have hsign : (-1 : ℚ)^(r-e) = (-1 : ℚ)^r * (-1 : ℚ)^e := by
    calc
      (-1 : ℚ)^(r-e) = (-1 : ℚ)^(r-e) * ((-1 : ℚ)^e)^2 := by
        rw [← pow_mul]
        norm_num
      _ = _ := by
        have hex : r-e+e*2=r+e := by omega
        rw [← pow_mul, ← pow_add, hex, pow_add]
  have hexp := symmetricParity_exponent r e her
  rw [div_eq_mul_inv]
  field_simp
  have hpow : (q : ℚ)^((r-e)*(r-e-1)/2) *
      (q : ℚ)^(e*(e+1)/2) * (q : ℚ)^(e*(r-e)) =
      (q : ℚ)^(r*(r-1)/2) * (q : ℚ)^e := by
    rw [← pow_add, ← pow_add, hexp, pow_add]
  rw [show (-(q : ℚ))^e = (-1 : ℚ)^e * (q : ℚ)^e by
    rw [show -(q : ℚ)=(-1 : ℚ)*(q : ℚ) by ring, mul_pow]]
  calc
    _ = (gaussianPascal q r e : ℚ) * ((-1 : ℚ)^r * (-1 : ℚ)^e) *
        ((q : ℚ)^(r*(r-1)/2) * (q : ℚ)^e) := by
          rw [← hpow, hsign]
          ring
    _ = _ := by ring


theorem reciprocalQAlternatingSum_recurrence (q n : ℕ) (hq : 1 < q) :
    reciprocalQAlternatingSum q (n+2) =
      (1-(q : ℚ))*reciprocalQAlternatingSum q (n+1) +
        (q : ℚ)*(1-((1 : ℚ)/(q : ℚ))^(n+1))*reciprocalQAlternatingSum q n := by
  have h := congrArg (Polynomial.eval (-(q : ℚ))) (reciprocalRogers_recurrence q n hq)
  simp only [reciprocalQAlternatingSum, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at h ⊢
  linear_combination h

theorem lowerTriangle_add_two (r : ℕ) :
    (r+2)*(r+2-1)/2 = r*(r-1)/2+(2*r+1) := by
  have h := natTriangle_add r 2
  unfold natTriangle at h
  norm_num at h ⊢
  omega

theorem symmetricParitySum_recurrence (q r : ℕ) (hq : 1 < q) :
    symmetricParitySum q (r+2) =
      (q : ℚ)^(r+1)*((q : ℚ)-1)*symmetricParitySum q (r+1) +
        (q : ℚ)^(r+1)*((q : ℚ)^(r+1)-1)*symmetricParitySum q r := by
  rw [symmetricParitySum_eq_reciprocal q (r+2) hq,
    reciprocalQAlternatingSum_recurrence q r hq,
    symmetricParitySum_eq_reciprocal q (r+1) hq,
    symmetricParitySum_eq_reciprocal q r hq]
  have hqn : (q : ℚ) ≠ 0 := by positivity
  rw [lowerTriangle_add_two]
  have htri1 : (r+1)*(r+1-1)/2=r*(r-1)/2+r := by
    have h := natTriangle_add r 1
    unfold natTriangle at h
    norm_num at h ⊢
    omega
  rw [htri1, pow_add]
  norm_num
  field_simp
  rw [show 2*r+1=r+(r+1) by omega, pow_add]
  ring

@[simp] theorem symmetricParitySum_zero (q : ℕ) : symmetricParitySum q 0=1 := by
  simp [symmetricParitySum, gaussianMobius, gaussianPascal_zero]

@[simp] theorem symmetricParitySum_one (q : ℕ) :
    symmetricParitySum q 1=(q : ℚ)-1 := by
  norm_num [symmetricParitySum, gaussianMobius, gaussianPascal, Finset.sum_range_succ]
  ring

theorem symmetricParitySum_odd_step (q u : ℕ) (hq : 1 < q) :
    symmetricParitySum q (2*u+1)=((q : ℚ)^(2*u+1)-1)*symmetricParitySum q (2*u) := by
  induction u with
  | zero => simp
  | succ u ih =>
      have heven : symmetricParitySum q (2*u+2)=
          (q : ℚ)^(2*u+2)*symmetricParitySum q (2*u+1) := by
        rw [symmetricParitySum_recurrence q (2*u) hq, ih]
        ring
      rw [show 2*(u+1)+1=(2*u+1)+2 by ring,
        symmetricParitySum_recurrence q (2*u+1) hq]
      rw [show 2*u+1+1=2*u+2 by omega, heven,
        show 2*(u+1)=2*u+2 by ring, heven, ih]
      ring

theorem symmetricParitySum_even_step (q u : ℕ) (hq : 1 < q) :
    symmetricParitySum q (2*u+2)=(q : ℚ)^(2*u+2)*symmetricParitySum q (2*u+1) := by
  rw [symmetricParitySum_recurrence q (2*u) hq,
    symmetricParitySum_odd_step q u hq]
  ring


noncomputable def zeroQuadraticIncidence (q d e : ℕ) : ℚ :=
  (q : ℚ)^(e*(e+1)/2) * (gaussianPascal q d e : ℚ)

noncomputable def zeroQuadraticKernel (q d r : ℕ) : ℚ :=
  QuadraticGeometry.rankIncidenceKernel q d (zeroQuadraticIncidence q d) r

theorem zeroQuadraticKernel_eq (q d r : ℕ) (hq : 1 < q) (hr : r ≤ d) :
    zeroQuadraticKernel q d r =
      (gaussianPascal q d r : ℚ) * symmetricParitySum q r := by
  unfold zeroQuadraticKernel QuadraticGeometry.rankIncidenceKernel
  unfold zeroQuadraticIncidence symmetricParitySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have her : e ≤ r := by simpa using Finset.mem_range.mp he
  have hf := gaussianPascal_flag q d r e hq hr her
  have hfc := congrArg (fun z : ℕ => (z : ℚ)) hf
  push_cast at hfc
  calc
    _ = gaussianMobius q (r-e) * (q : ℚ)^(e*(e+1)/2) *
        ((gaussianPascal q d e : ℚ) * (gaussianPascal q (d-e) (r-e) : ℚ)) := by ring
    _ = gaussianMobius q (r-e) * (q : ℚ)^(e*(e+1)/2) *
        ((gaussianPascal q d r : ℚ) * (gaussianPascal q r e : ℚ)) := by rw [hfc]
    _ = _ := by ring



theorem zeroQuadraticKernel_tail (q d r : ℕ) (hdr : d < r) :
    zeroQuadraticKernel q d r = 0 := by
  unfold zeroQuadraticKernel
  apply QuadraticGeometry.rankIncidenceKernel_tail
  · intro i hi
    unfold zeroQuadraticIncidence
    rw [gaussianPascal_eq_zero q d i hi]
    ring
  · exact hdr

noncomputable def zeroGroupedBlockA (q n : ℕ) : ℕ → ℚ
  | 0 => 1
  | u+1 => (gaussianPascal q (2*n+1) (2*u+2) : ℚ) * symmetricParitySum q (2*u+1)

noncomputable def zeroGroupedBlockB (q n u : ℕ) : ℚ :=
  (q : ℚ)^(2*n-2*u) * (gaussianPascal q (2*n) (2*u) : ℚ) *
    symmetricParitySum q (2*u)

theorem zeroQuadraticKernel_groupedA (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n) :
    QuadraticGeometry.groupedRankKernelA (zeroQuadraticKernel q (2*n)) u =
      zeroGroupedBlockA q n u := by
  cases u with
  | zero =>
      simp only [QuadraticGeometry.groupedRankKernelA, zeroGroupedBlockA]
      rw [zeroQuadraticKernel_eq q (2*n) 0 hq (by omega)]
      simp [gaussianPascal_zero]
  | succ u =>
      simp only [QuadraticGeometry.groupedRankKernelA, zeroGroupedBlockA]
      rw [zeroQuadraticKernel_eq q (2*n) (2*u+1) hq (by omega),
        zeroQuadraticKernel_eq q (2*n) (2*u+2) hq (by omega),
        symmetricParitySum_even_step q u hq]
      have hp := gaussianPascal_succ q (2*n) (2*u+1)
      rw [show 2*n+1=2*n+1 by rfl, show 2*u+1+1=2*u+2 by omega] at hp
      rw [hp]
      push_cast
      ring

theorem zeroQuadraticKernel_groupedB (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n) :
    QuadraticGeometry.groupedRankKernelB (zeroQuadraticKernel q (2*n)) u =
      zeroGroupedBlockB q n u := by
  simp only [QuadraticGeometry.groupedRankKernelB, zeroGroupedBlockB]
  rw [zeroQuadraticKernel_eq q (2*n) (2*u) hq (by omega)]
  by_cases hun : u=n
  · subst u
    rw [zeroQuadraticKernel_tail q (2*n) (2*n+1) (by omega)]
    simp [gaussianPascal_self]
  · have hul : u<n := by omega
    rw [zeroQuadraticKernel_eq q (2*n) (2*u+1) hq (by omega),
      symmetricParitySum_odd_step q u hq]
    have hr := gaussianPascal_ratio q (2*n) (2*u) hq (by omega)
    calc
      (gaussianPascal q (2*n) (2*u) : ℚ) * symmetricParitySum q (2*u) +
          (gaussianPascal q (2*n) (2*u+1) : ℚ) *
            (((q : ℚ)^(2*u+1)-1)*symmetricParitySum q (2*u)) =
        ((gaussianPascal q (2*n) (2*u) : ℚ) *
          ((q : ℚ)^(2*n-2*u)-1) +
          (gaussianPascal q (2*n) (2*u) : ℚ)) * symmetricParitySum q (2*u) := by
            rw [← hr]
            ring
      _ = _ := by ring


noncomputable def zeroNewtonBlockA (q n u : ℕ) : ℚ :=
  (gaussianPascal (q^2) n u : ℚ) *
    gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n+1)) u

noncomputable def zeroNewtonBlockB (q n u : ℕ) : ℚ :=
  (q : ℚ)^(2*n) * (gaussianPascal (q^2) n u : ℚ) *
    gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u

noncomputable def symmetricOddBlock (q : ℕ) : ℕ → ℚ
  | 0 => 1
  | u+1 => symmetricParitySum q (2*u+1)

theorem symmetricOddBlock_succ (q u : ℕ) (hq : 1 < q) :
    symmetricOddBlock q (u+1) =
      (q : ℚ)^(2*u) * ((q : ℚ)^(2*u+1)-1) * symmetricOddBlock q u := by
  cases u with
  | zero => simp [symmetricOddBlock]
  | succ u =>
      simp only [symmetricOddBlock]
      rw [symmetricParitySum_odd_step q (u+1) hq]
      rw [show 2*(u+1)=2*u+2 by ring,
        symmetricParitySum_even_step q u hq]
      ring



theorem zeroGroupedBlockA_eq (q n u : ℕ) :
    zeroGroupedBlockA q n u =
      (gaussianPascal q (2*n+1) (2*u) : ℚ) * symmetricOddBlock q u := by
  cases u with
  | zero => simp [zeroGroupedBlockA, symmetricOddBlock, gaussianPascal_zero]
  | succ u =>
      simp only [zeroGroupedBlockA, symmetricOddBlock]
      rw [show 2*(u+1)=2*u+2 by ring]

theorem zeroGroupedBlockA_cross_succ (q n u : ℕ) (hq : 1 < q) (hu : u < n) :
    zeroGroupedBlockA q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u) * ((q : ℚ)^(2*n+1-2*u)-1) *
        ((q : ℚ)^(2*n-2*u)-1) * zeroGroupedBlockA q n u := by
  rw [zeroGroupedBlockA_eq, zeroGroupedBlockA_eq,
    symmetricOddBlock_succ q u hq]
  have hr1 := gaussianPascal_ratio q (2*n+1) (2*u) hq (by omega)
  have hr2 := gaussianPascal_ratio q (2*n+1) (2*u+1) hq (by omega)
  rw [show 2*u+1+1=2*u+2 by omega] at hr2
  calc
    _ = ((gaussianPascal q (2*n+1) (2*u+2) : ℚ) *
          ((q : ℚ)^(2*u+2)-1)) *
        ((q : ℚ)^(2*u) * ((q : ℚ)^(2*u+1)-1) * symmetricOddBlock q u) := by ring
    _ = ((gaussianPascal q (2*n+1) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*n+1-(2*u+1))-1)) *
        ((q : ℚ)^(2*u) * ((q : ℚ)^(2*u+1)-1) * symmetricOddBlock q u) := by rw [hr2]
    _ = (q : ℚ)^(2*u) * ((q : ℚ)^(2*n-2*u)-1) *
        ((gaussianPascal q (2*n+1) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*u+1)-1)) * symmetricOddBlock q u := by
            rw [show 2*n+1-(2*u+1)=2*n-2*u by omega]
            ring
    _ = _ := by rw [hr1]; ring


theorem zeroNewtonBlockA_cross_succ (q n u : ℕ) (hq : 1 < q) (hu : u < n) :
    zeroNewtonBlockA q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u) * ((q : ℚ)^(2*n+1-2*u)-1) *
        ((q : ℚ)^(2*n-2*u)-1) * zeroNewtonBlockA q n u := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hr := gaussianPascal_ratio (q^2) n u hq2 hu
  norm_num only [Nat.cast_pow] at hr
  rw [show ((q : ℚ)^2)^(u+1)=(q : ℚ)^(2*u+2) by
    rw [←pow_mul, show 2*(u+1)=2*u+2 by ring]] at hr
  rw [show ((q : ℚ)^2)^(n-u)=(q : ℚ)^(2*n-2*u) by
    rw [←pow_mul]; congr 1; omega] at hr
  have hg : (q : ℚ)^(2*n+1) - (((q^2 : ℕ) : ℚ)^u) =
      (q : ℚ)^(2*u)*((q : ℚ)^(2*n+1-2*u)-1) := by
    norm_num only [Nat.cast_pow]
    rw [show ((q : ℚ)^2)^u=(q : ℚ)^(2*u) by rw [←pow_mul]]
    have he : 2*n+1=2*u+(2*n+1-2*u) := by omega
    conv_lhs => rw [he]
    rw [pow_add]
    ring
  have hn : gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n+1)) (u+1) =
      gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n+1)) u *
        ((q : ℚ)^(2*n+1) - (((q^2 : ℕ) : ℚ)^u)) := by
    exact Finset.prod_range_succ _ _
  unfold zeroNewtonBlockA
  rw [hn, hg]
  calc
    _ = ((gaussianPascal (q^2) n (u+1) : ℚ) *
          ((q : ℚ)^(2*u+2)-1)) *
        (gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n+1)) u *
          ((q : ℚ)^(2*u)*((q : ℚ)^(2*n+1-2*u)-1))) := by ring
    _ = _ := by rw [hr]; ring

theorem zeroGroupedBlockA_eq_newton (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n) :
    zeroGroupedBlockA q n u = zeroNewtonBlockA q n u := by
  induction u with
  | zero => simp [zeroGroupedBlockA, zeroNewtonBlockA, gaussianNewtonProduct,
      gaussianPascal_zero]
  | succ u ih =>
      have hult : u < n := by omega
      have hL := zeroGroupedBlockA_cross_succ q n u hq hult
      have hR := zeroNewtonBlockA_cross_succ q n u hq hult
      have hden : (q : ℚ)^(2*u+2)-1 ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by exact_mod_cast hq) (by omega)))
      apply mul_right_cancel₀ hden
      rw [hL, hR, ih (by omega)]


noncomputable def zeroEvenBlock (q n u : ℕ) : ℚ :=
  (gaussianPascal q (2*n) (2*u) : ℚ) * symmetricParitySum q (2*u)

noncomputable def zeroEvenNewtonBlock (q n u : ℕ) : ℚ :=
  (q : ℚ)^(2*u) * (gaussianPascal (q^2) n u : ℚ) *
    gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u

theorem zeroEvenBlock_cross_succ (q n u : ℕ) (hq : 1 < q) (hu : u < n) :
    zeroEvenBlock q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-2*u)-1) *
        ((q : ℚ)^(2*n-2*u-1)-1) * zeroEvenBlock q n u := by
  unfold zeroEvenBlock
  rw [show 2*(u+1)=2*u+2 by ring,
    symmetricParitySum_even_step q u hq,
    symmetricParitySum_odd_step q u hq]
  have hr1 := gaussianPascal_ratio q (2*n) (2*u) hq (by omega)
  have hr2 := gaussianPascal_ratio q (2*n) (2*u+1) hq (by omega)
  rw [show 2*u+1+1=2*u+2 by omega] at hr2
  calc
    _ = ((gaussianPascal q (2*n) (2*u+2) : ℚ) *
          ((q : ℚ)^(2*u+2)-1)) *
        ((q : ℚ)^(2*u+2) * ((q : ℚ)^(2*u+1)-1) *
          symmetricParitySum q (2*u)) := by ring
    _ = ((gaussianPascal q (2*n) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*n-(2*u+1))-1)) *
        ((q : ℚ)^(2*u+2) * ((q : ℚ)^(2*u+1)-1) *
          symmetricParitySum q (2*u)) := by rw [hr2]
    _ = (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-2*u-1)-1) *
        ((gaussianPascal q (2*n) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*u+1)-1)) * symmetricParitySum q (2*u) := by
            rw [show 2*n-(2*u+1)=2*n-2*u-1 by omega]
            ring
    _ = _ := by rw [hr1]; ring

theorem zeroEvenNewtonBlock_cross_succ (q n u : ℕ) (hq : 1 < q) (hu : u < n) :
    zeroEvenNewtonBlock q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-2*u)-1) *
        ((q : ℚ)^(2*n-2*u-1)-1) * zeroEvenNewtonBlock q n u := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hr := gaussianPascal_ratio (q^2) n u hq2 hu
  norm_num only [Nat.cast_pow] at hr
  rw [show ((q : ℚ)^2)^(u+1)=(q : ℚ)^(2*u+2) by
    rw [←pow_mul, show 2*(u+1)=2*u+2 by ring]] at hr
  rw [show ((q : ℚ)^2)^(n-u)=(q : ℚ)^(2*n-2*u) by
    rw [←pow_mul]; congr 1; omega] at hr
  have hg : (q : ℚ)^(2*n-1)-(((q^2 : ℕ) : ℚ)^u)=
      (q : ℚ)^(2*u)*((q : ℚ)^(2*n-2*u-1)-1) := by
    norm_num only [Nat.cast_pow]
    rw [show ((q : ℚ)^2)^u=(q : ℚ)^(2*u) by rw [←pow_mul]]
    have he : 2*n-1=2*u+(2*n-2*u-1) := by omega
    conv_lhs => rw [he]
    rw [pow_add]
    ring
  have hn : gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) (u+1)=
      gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u *
        ((q : ℚ)^(2*n-1)-(((q^2 : ℕ) : ℚ)^u)) := by
    exact Finset.prod_range_succ _ _
  unfold zeroEvenNewtonBlock
  rw [hn, hg]
  calc
    _ = (q : ℚ)^(2*u+2) *
        ((gaussianPascal (q^2) n (u+1) : ℚ) * ((q : ℚ)^(2*u+2)-1)) *
        (gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u *
          ((q : ℚ)^(2*u)*((q : ℚ)^(2*n-2*u-1)-1))) := by ring
    _ = _ := by rw [hr]; ring

theorem zeroEvenBlock_eq_newton (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n) :
    zeroEvenBlock q n u = zeroEvenNewtonBlock q n u := by
  induction u with
  | zero => simp [zeroEvenBlock, zeroEvenNewtonBlock, gaussianNewtonProduct,
      gaussianPascal_zero]
  | succ u ih =>
      have hult : u < n := by omega
      have hL := zeroEvenBlock_cross_succ q n u hq hult
      have hR := zeroEvenNewtonBlock_cross_succ q n u hq hult
      have hden : (q : ℚ)^(2*u+2)-1 ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by exact_mod_cast hq) (by omega)))
      apply mul_right_cancel₀ hden
      rw [hL, hR, ih (by omega)]

theorem zeroGroupedBlockB_eq_newton (q n u : ℕ) (hq : 1 < q) (hu : u ≤ n) :
    zeroGroupedBlockB q n u = zeroNewtonBlockB q n u := by
  unfold zeroGroupedBlockB zeroNewtonBlockB
  calc
    (q : ℚ)^(2*n-2*u) * (gaussianPascal q (2*n) (2*u) : ℚ) *
        symmetricParitySum q (2*u) =
      (q : ℚ)^(2*n-2*u) * zeroEvenBlock q n u := by
        unfold zeroEvenBlock
        ring
    _ = (q : ℚ)^(2*n-2*u) * zeroEvenNewtonBlock q n u := by
      rw [zeroEvenBlock_eq_newton q n u hq hu]
    _ = _ := by
      unfold zeroEvenNewtonBlock
      have he : 2*n-2*u+2*u=2*n := by omega
      calc
        (q : ℚ)^(2*n-2*u) * ((q : ℚ)^(2*u) *
            (gaussianPascal (q^2) n u : ℚ) *
            gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u) =
          (q : ℚ)^(2*n-2*u+2*u) * (gaussianPascal (q^2) n u : ℚ) *
            gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u := by
              rw [pow_add]
              ring
        _ = _ := by rw [he]


theorem gaussianPascal_weighted_newton (Q n j : ℕ) (hQ : 1 < Q) (hj : j ≤ n)
    (gamma : ℚ) :
    (∑ u ∈ Finset.range (j+1),
      (gaussianPascal Q (n-u) (j-u) : ℚ) *
        ((gaussianPascal Q n u : ℚ) * gaussianNewtonProduct Q gamma u)) =
      (gaussianPascal Q n j : ℚ) * gamma^j := by
  calc
    _ = (gaussianPascal Q n j : ℚ) *
        (∑ u ∈ Finset.range (j+1),
          (gaussianPascal Q j u : ℚ) * gaussianNewtonProduct Q gamma u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have huj : u ≤ j := by simpa using Finset.mem_range.mp hu
      have hf := gaussianPascal_flag Q n j u hQ hj huj
      have hfc := congrArg (fun z : ℕ => (z : ℚ)) hf
      push_cast at hfc
      calc
        _ = ((gaussianPascal Q n u : ℚ) * (gaussianPascal Q (n-u) (j-u) : ℚ)) *
            gaussianNewtonProduct Q gamma u := by ring
        _ = ((gaussianPascal Q n j : ℚ) * (gaussianPascal Q j u : ℚ)) *
            gaussianNewtonProduct Q gamma u := by rw [hfc]
        _ = _ := by ring
    _ = _ := by rw [gaussianPascal_newton]

theorem gaussianWeighted_newton (Q n j : ℕ) (hQ : 1 < Q) (hj : j ≤ n)
    (gamma : ℚ) :
    gaussianWeightedSum Q n j (fun u =>
      (gaussianPascal Q n u : ℚ) * gaussianNewtonProduct Q gamma u) =
      (gaussianPascal Q n j : ℚ) * gamma^j := by
  unfold gaussianWeightedSum
  calc
    _ = ∑ u ∈ Finset.range (j+1),
        (gaussianPascal Q (n-u) (j-u) : ℚ) *
          ((gaussianPascal Q n u : ℚ) * gaussianNewtonProduct Q gamma u) := by
      apply Finset.sum_congr rfl
      intro u hu
      have huj : u ≤ j := by simpa using Finset.mem_range.mp hu
      rw [gaussianBinomial_eq_gaussianPascal Q (n-u) (j-u) hQ]
    _ = _ := gaussianPascal_weighted_newton Q n j hQ hj gamma

theorem zeroQuadraticKernel_weightedA (q n j : ℕ) (hq : 1 < q) (hj : j ≤ n) :
    gaussianWeightedSum (q^2) n j
      (QuadraticGeometry.groupedRankKernelA (zeroQuadraticKernel q (2*n))) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) n j : ℚ) := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hfun : QuadraticGeometry.groupedRankKernelA (zeroQuadraticKernel q (2*n)) =
      fun u => (gaussianPascal (q^2) n u : ℚ) *
        gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n+1)) u := by
    funext u
    by_cases hu : u ≤ n
    · rw [zeroQuadraticKernel_groupedA q n u hq hu,
        zeroGroupedBlockA_eq_newton q n u hq hu]
      rfl
    · cases u with
      | zero => omega
      | succ u =>
          simp only [QuadraticGeometry.groupedRankKernelA]
          rw [zeroQuadraticKernel_tail q (2*n) (2*u+1) (by omega),
            zeroQuadraticKernel_tail q (2*n) (2*u+2) (by omega),
            gaussianPascal_eq_zero (q^2) n (u+1) (by omega)]
          ring
  rw [hfun, gaussianWeighted_newton (q^2) n j hq2 hj]
  rw [← pow_mul]
  ring

theorem zeroQuadraticKernel_weightedB (q n j : ℕ) (hq : 1 < q) (hj : j ≤ n) :
    gaussianWeightedSum (q^2) n j
      (QuadraticGeometry.groupedRankKernelB (zeroQuadraticKernel q (2*n))) =
      (q : ℚ)^(2*n+(2*n-1)*j) * (gaussianPascal (q^2) n j : ℚ) := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hfun : QuadraticGeometry.groupedRankKernelB (zeroQuadraticKernel q (2*n)) =
      fun u => (q : ℚ)^(2*n) * ((gaussianPascal (q^2) n u : ℚ) *
        gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u) := by
    funext u
    by_cases hu : u ≤ n
    · rw [zeroQuadraticKernel_groupedB q n u hq hu,
        zeroGroupedBlockB_eq_newton q n u hq hu]
      unfold zeroNewtonBlockB
      ring
    · unfold QuadraticGeometry.groupedRankKernelB
      rw [zeroQuadraticKernel_tail q (2*n) (2*u) (by omega),
        zeroQuadraticKernel_tail q (2*n) (2*u+1) (by omega),
        gaussianPascal_eq_zero (q^2) n u (by omega)]
      ring
  rw [hfun]
  have hs : gaussianWeightedSum (q^2) n j (fun u =>
      (q : ℚ)^(2*n) * ((gaussianPascal (q^2) n u : ℚ) *
        gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u)) =
      (q : ℚ)^(2*n) * gaussianWeightedSum (q^2) n j (fun u =>
        (gaussianPascal (q^2) n u : ℚ) *
          gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u) := by
    unfold gaussianWeightedSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hs, gaussianWeighted_newton (q^2) n j hq2 hj]
  rw [← pow_mul]
  ring

end BinaryFieldCounterexamples
