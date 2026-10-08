/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform numerical bounds for higher-rate lengthening
A fixed smaller quadratic exponent absorbs the dimension shift and linear losses.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.HigherRateLengthening
open Filter
open scoped Topology

/-- The selected integer list size has a quadratic logarithm. -/
theorem selected_list_log_bound (a : ℝ) (ha : a ≤ 1) (d : ℕ) :
    Real.log (2 * (2 ^ ⌊a * (d : ℝ)^2⌋₊ : ℕ)) ≤
      ((d : ℝ)^2 + 1) * Real.log 2 := by
  have hfN : ⌊a * (d : ℝ)^2⌋₊ ≤ d^2 := Nat.floor_le_of_le (by
    push_cast
    exact mul_le_of_le_one_left (sq_nonneg _) ha)
  have hf : (⌊a * (d : ℝ)^2⌋₊ : ℝ) ≤ (d : ℝ)^2 := by exact_mod_cast hfN
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  nlinarith

/-- A smaller quadratic exponent absorbs a fixed codimension and linear loss. -/
theorem selected_list_bounds (alpha C : ℝ) (hα : 0 < alpha) (hα1 : alpha ≤ 1)
    (hC : 0 ≤ C) (r : ℕ) :
    let a := alpha / 8
    let A := a / (2 * Real.log 2)
    0 < A ∧ ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → r ≤ d ∧
      (2 ^ ⌊a * (d : ℝ)^2⌋₊ : ℕ) ≤ 2 ^ (d^2) ∧
      ((2^d : ℕ) : ℝ) ^ (A * Real.log (2^d : ℕ)) ≤
        (2 ^ ⌊a * (d : ℝ)^2⌋₊ : ℕ) ∧
      ((2 ^ ⌊a * (d : ℝ)^2⌋₊ : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (alpha * ((d-r : ℕ) : ℝ)^2 - C * (d-r)) := by
  dsimp only
  have ha : 0 < alpha / 8 := by positivity
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨by positivity, ?_⟩
  obtain ⟨d0, hd0⟩ := exists_nat_ge (max (max (2 * (r : ℝ)) (8*C/alpha))
    (max 1 (16/alpha)))
  refine ⟨d0, ?_⟩
  intro d hd
  have hdd : (d0 : ℝ) ≤ d := by exact_mod_cast hd
  have hdr : 2*(r : ℝ) ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans (hd0.trans hdd))
  have hdC : 8*C/alpha ≤ d := (le_max_right _ _).trans ((le_max_left _ _).trans (hd0.trans hdd))
  have hd1 : (1 : ℝ) ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans (hd0.trans hdd))
  have hda : 16/alpha ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans (hd0.trans hdd))
  have hrd : r ≤ d := by exact_mod_cast (by linarith : (r : ℝ) ≤ d)
  have hsub : ((d-r : ℕ) : ℝ) = (d : ℝ)-r := Nat.cast_sub hrd
  have hdSq : (d : ℝ) ≤ (d : ℝ)^2 := by nlinarith
  have hCd : 8*C ≤ (d : ℝ)*alpha := (div_le_iff₀ hα).mp hdC
  have haD : 16 ≤ (d : ℝ)*alpha := (div_le_iff₀ hα).mp hda
  have hfloorU : (⌊alpha/8*(d : ℝ)^2⌋₊ : ℝ) ≤ alpha/8*(d : ℝ)^2 :=
    Nat.floor_le (by positivity)
  have hfloorL : alpha/8*(d : ℝ)^2-1 ≤ (⌊alpha/8*(d : ℝ)^2⌋₊ : ℝ) :=
    (Nat.sub_one_lt_floor _).le
  have he : alpha/8*(d : ℝ)^2 ≤ alpha*((d : ℝ)-r)^2-C*((d : ℝ)-r) := by
    have hx : (d : ℝ)^2/4 ≤ ((d : ℝ)-r)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hx hα.le
    have hc : C*((d : ℝ)-r) ≤ C*d := mul_le_mul_of_nonneg_left (by linarith [show (0:ℝ)≤r by positivity]) hC
    have hc2 : C*d ≤ alpha*(d : ℝ)^2/8 := by linarith [mul_nonneg (by linarith : 0 ≤ alpha*d-8*C) (show (0:ℝ)≤d by positivity)]
    linarith
  refine ⟨hrd, ?_, ?_, ?_⟩
  · apply Nat.pow_le_pow_right (by decide)
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_left (sq_nonneg _) (by linarith)
  · have hf : alpha/16*(d : ℝ)^2 ≤ (⌊alpha/8*(d : ℝ)^2⌋₊ : ℝ) := by
      have hh : 16 ≤ alpha*(d : ℝ)^2 := by linarith [mul_le_mul_of_nonneg_left hdSq hα.le]
      linarith
    have heq : ((2^d : ℕ) : ℝ) ^ (alpha/8/(2*Real.log 2)*Real.log (2^d : ℕ)) =
        (2:ℝ)^(alpha/16*(d:ℝ)^2) := by
      push_cast
      rw [Real.log_pow, ←Real.rpow_natCast, ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      congr 1
      field_simp
      ring
    rw [heq]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hf)
  · rw [hsub]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (hfloorU.trans he))

/-- The normalized finite agreement bound keeps the rate curve, with
explicit seed, sampling, and integer-rounding errors. -/
theorem normalized_lengthening_lower (N M a T J L : ℕ) (rho delta : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (ha : a ≤ M) (hL : 1 ≤ L)
    (hdelta : 0 ≤ delta) (hseed : 1/2-(T:ℝ)/M ≤ delta)
    (hJ : rho*N-1 ≤ (J:ℝ)) (haeq : (a:ℝ)=(J:ℝ)-N+3*M/4) :
    let U : ℝ := N-M+a+T-((a:ℝ)*T/M+Real.sqrt (((a:ℝ)/2)*Real.log (2*L)))
    (1+rho)/2-((M:ℝ)/N)/8-
      (delta+Real.sqrt (Real.log (2*L)/(2*N))+3/(2*N)) ≤ (⌊U⌋₊:ℝ)/N := by
  dsimp only
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hMNr : (M:ℝ)≤N := by exact_mod_cast hMN
  have har : (a:ℝ)≤M := by exact_mod_cast ha
  have hl : 0≤Real.log (2*(L:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤2*L))
  have hform : (N:ℝ)-M+a+T-(a:ℝ)*T/M = N-M+a+((M:ℝ)-a)*((T:ℝ)/M) := by
    field_simp
    ring
  have hseedmul := mul_le_mul_of_nonneg_left (by linarith : (1/2:ℝ)-delta≤(T:ℝ)/M)
    (by linarith : (0:ℝ)≤M-a)
  have herr := mul_le_mul_of_nonneg_right (by linarith : (M:ℝ)-a≤N) hdelta
  have hcore : (N:ℝ)*((1+rho)/2-((M:ℝ)/N)/8)-1/2-N*delta ≤
      (N:ℝ)-M+a+T-(a:ℝ)*T/M := by
    rw [hform]
    have heq : (N:ℝ)*((1+rho)/2-((M:ℝ)/N)/8) = N*(1+rho)/2-M/8 := by
      field_simp
    rw [heq]
    linarith
  have hsqrt : Real.sqrt (((a:ℝ)/2)*Real.log (2*L)) ≤
      (N:ℝ)*Real.sqrt (Real.log (2*L)/(2*N)) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have heq : (N:ℝ)^2*(Real.log (2*L)/(2*N)) = N/2*Real.log (2*L) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by linarith) hl
  have hfloor := (Nat.sub_one_lt_floor ((N:ℝ)-M+a+T-
    ((a:ℝ)*T/M+Real.sqrt (((a:ℝ)/2)*Real.log (2*L))))).le
  apply (le_div_iff₀ hNr).mpr
  have heq : ((1+rho)/2-((M:ℝ)/N)/8-
      (delta+Real.sqrt (Real.log (2*L)/(2*N))+3/(2*N)))*(N:ℝ) =
      (N:ℝ)*((1+rho)/2-((M:ℝ)/N)/8)-N*delta-
        N*Real.sqrt (Real.log (2*L)/(2*N))-3/2 := by
    field_simp
    ring
  rw [heq]
  linarith

/-- Seed deficit, padding deviation, and the two rounding losses vanish
uniformly in the rate and the prescribed domain. -/
theorem lengthening_error_tendsto (C theta : ℝ) (htheta : 0 < theta) (r : ℕ) :
    Tendsto (fun d : ℕ => C * ((2^(d-r) : ℕ) : ℝ)^(-theta) +
      Real.sqrt ((((d : ℝ)^2+1)*Real.log 2)/(2*((2^d : ℕ) : ℝ))) +
      3/(2*((2^d : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun d : ℕ => (2 : ℝ)^d) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hseed := ((tendsto_rpow_neg_atTop htheta).comp
    (hpow.comp (tendsto_sub_atTop_nat r))).const_mul C
  have hquad := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)
  have hone := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have hinside : Tendsto (fun d : ℕ => (((d:ℝ)^2+1)*Real.log 2)/(2*(2:ℝ)^d))
      atTop (𝓝 0) := by
    convert (hquad.add hone).mul_const (Real.log 2/2) using 1 <;>
      simp only [pow_zero, zero_add, zero_mul]
    funext d
    ring
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hround : Tendsto (fun d : ℕ => 3/(2*(2:ℝ)^d)) atTop (𝓝 0) := by
    convert hone.mul_const (3/2:ℝ) using 1 <;> simp only [pow_zero, zero_mul]
    funext d
    ring
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_zero, Real.sqrt_zero, zero_add, Function.comp_def]
    using (hseed.add hsqrt).add hround

end BinaryFieldCounterexamples.HigherRateLengthening
