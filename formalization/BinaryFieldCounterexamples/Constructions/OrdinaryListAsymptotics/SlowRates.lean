/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.OrdinaryListAsymptotics.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Numerical identities and limits for slowly vanishing rates

For `b=2^u`, `n=2u`, and `t=u`, the length is `2^(4u²)`. The list exponent
`u/2` tends to infinity, the rate tends to zero, and the normalized agreement
deficit tends to zero. These are separate from the fixed-base corollary.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.OrdinaryListConstruction
open Filter
open scoped Topology

/-- The growing-base extension has exactly the stated length. -/
theorem slow_rate_length (u : ℕ) : (2^u)^(2*(2*u)) = 2^(4*u^2) := by
  rw [←pow_mul]
  congr 1
  ring

/-- The Gaussian leading power is `N^(u/2)` at the growing-base parameters. -/
theorem slow_rate_list_power (u : ℕ) :
    ((2:ℝ)^(4*u^2))^((u:ℝ)/2) = ((2^u:ℕ):ℝ)^(2*u*(2*u-u)) := by
  push_cast
  rw [←Real.rpow_natCast (2:ℝ) (4*u^2),←Real.rpow_mul (by norm_num)]
  rw [←pow_mul,←Real.rpow_natCast]
  congr 1
  simp only [show 2*u-u=u by omega]
  push_cast
  ring

/-- The normalized agreement has the exact relative deficit printed in the paper. -/
theorem slow_rate_relative_agreement (u : ℕ) (hu : 2 ≤ u) :
    ((((2^u)^(2*(2*u)-1)-(2^u-1)*(2^u)^(2*(2*u)-u-1):ℕ):ℝ)/
      (2:ℝ)^(4*u^2)) / Real.sqrt (1/((2^u:ℕ):ℝ)^2) =
      1-((2:ℝ)^u-1)/(2:ℝ)^(u^2) := by
  have hb : 2 ≤ 2^u := by
    simpa using (Nat.pow_le_pow_right (by decide : 0<2) (show 1≤u by omega))
  have hf := fullfield_agreement_fraction (2^u) (2*u) u hb (by omega) (by omega)
  have hN : (((2^u)^(2*(2*u)):ℕ):ℝ)=(2:ℝ)^(4*u^2) := by
    rw [slow_rate_length]; push_cast; rfl
  have hN' : ((2^u:ℕ):ℝ)^(2*(2*u))=(2:ℝ)^(4*u^2) := by exact_mod_cast hN
  rw [hN'] at hf
  rw [hf]
  have hs : Real.sqrt (1/((2^u:ℕ):ℝ)^2)=1/((2^u:ℕ):ℝ) := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_sq_eq_abs,abs_of_pos (by positivity)]
  rw [hs]
  push_cast
  have hp : ((2:ℝ)^u)^(u+1)=(2:ℝ)^(u^2)*(2:ℝ)^u := by
    rw [pow_succ,←pow_mul]
    congr 2
    ring
  rw [hp]
  field_simp

/-- The rate is an exponential tending to zero. -/
theorem slow_rate_tendsto_zero :
    Tendsto (fun u : ℕ => 1/((2:ℝ)^u)^2) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4)
    (by norm_num : (1/4:ℝ)<1)
  convert h using 1
  funext u
  rw [div_pow,one_pow,←pow_mul,show (4:ℝ)=2^2 by norm_num,←pow_mul]
  rw [Nat.mul_comm]

/-- The relative deficit is bounded by a geometric sequence for `u ≥ 2`. -/
theorem slow_rate_relative_deficit_bound (u : ℕ) (hu : 2 ≤ u) :
    0 ≤ ((2:ℝ)^u-1)/(2:ℝ)^(u^2) ∧
      ((2:ℝ)^u-1)/(2:ℝ)^(u^2) ≤ (1/2:ℝ)^u := by
  have hp : (1:ℝ)≤2^u := one_le_pow₀ (by norm_num)
  constructor
  · positivity
  · have he : u+u ≤ u^2 := by nlinarith
    have hpow : (2:ℝ)^u*(2:ℝ)^u ≤ (2:ℝ)^(u^2) := by
      rw [←pow_add]
      exact pow_le_pow_right₀ (by norm_num) he
    rw [div_pow,one_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith [show (0:ℝ)≤2^u by positivity]

/-- Agreement approaches the shrinking Johnson threshold in relative terms. -/
theorem slow_rate_relative_agreement_tendsto_one :
    Tendsto (fun u : ℕ => 1-((2:ℝ)^u-1)/(2:ℝ)^(u^2)) atTop (𝓝 1) := by
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hd : Tendsto (fun u : ℕ => ((2:ℝ)^u-1)/(2:ℝ)^(u^2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    · filter_upwards [eventually_ge_atTop 2] with u hu
      exact (slow_rate_relative_deficit_bound u hu).1
    · filter_upwards [eventually_ge_atTop 2] with u hu
      exact (slow_rate_relative_deficit_bound u hu).2
  simpa using tendsto_const_nhds.sub hd

/-- The lower-bound exponent itself diverges, making the lists superpolynomial. -/
theorem slow_rate_list_exponent_tendsto_atTop :
    Tendsto (fun u : ℕ => (u:ℝ)/2) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)

/-- The rate has the printed length-relative exponent `-1/(2u)`. -/
theorem slow_rate_as_power_of_length (u : ℕ) (hu : 0<u) :
    1/((2:ℝ)^u)^2 = ((2:ℝ)^(4*u^2))^(-1/(2*(u:ℝ))) := by
  rw [←Real.rpow_natCast (2:ℝ) (4*u^2),←Real.rpow_mul (by norm_num)]
  have he : ((4*u^2:ℕ):ℝ)*(-1/(2*(u:ℝ)))=-((2*u:ℕ):ℝ) := by
    push_cast
    field_simp
    ring
  rw [he,Real.rpow_neg (by norm_num),Real.rpow_natCast]
  simp only [one_div,←pow_mul,Nat.mul_comm]
end BinaryFieldCounterexamples.OrdinaryListConstruction
