/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.RateParameters
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.AsymptoticBounds

/-!
# Exact rate and asymptotic bounds for Gold padding at every fixed rate

Padding outside the smaller seed domain needs only integer floor estimates.
There is no balancing or sampling loss in the resulting agreement fraction.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.GoldAllRates
open Filter
open scoped Topology

/-- The seed degree bound has exactly the required fraction of the full domain. -/
theorem seed_quarter_ratio (r d : ℕ) (hrd : r + 2 ≤ d) :
    ((2^(d-r)/4 : ℕ) : ℝ) / (2^d : ℕ) = 1 / (2^(r+2) : ℕ) := by
  rw [HigherRateLengthening.seed_quarter_cast r d hrd]
  have hratio := HigherRateLengthening.seed_size_ratio r d (by omega)
  have hp : ((2^(r+2) : ℕ) : ℝ) = (2^r : ℕ) * 4 := by
    rw [pow_add]
    push_cast
    norm_num
  rw [hp]
  calc
    ((2^(d-r) : ℕ) : ℝ) / 4 / (2^d : ℕ) =
        (((2^(d-r) : ℕ) : ℝ) / (2^d : ℕ)) / 4 := by ring
    _ = 1 / (2^r : ℕ) / 4 := by rw [hratio]
    _ = 1 / ((2^r : ℕ) * 4) := by ring

/-- The fixed-rate interval supplies enough degree and enough points outside
the seed domain for padding, without any natural-subtraction truncation. -/
theorem rate_parameters (r d : ℕ) (hrd : r + 2 ≤ d) (rho : ℝ)
    (hrhopos : 0 < rho) (hrholt : rho < 1)
    (hquarterrho : 1 / (2^(r+2) : ℕ) < rho)
    (hquartercomplement : 1 / (2^(r+2) : ℕ) < (1-rho)/3) :
    let N : ℕ := 2^d
    let M : ℕ := 2^(d-r)
    let J := ⌊rho*(N : ℝ)⌋₊
    M/4 ≤ J ∧ J ≤ N ∧ J-M/4 ≤ N-M ∧ M ≤ N := by
  dsimp only
  have hMN : (2^(d-r) : ℕ) ≤ 2^d :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hNpos : (0 : ℝ) < (2^d : ℕ) := by positivity
  have hquarter := HigherRateLengthening.seed_quarter_cast r d hrd
  have hratio := seed_quarter_ratio r d hrd
  have hKreal : ((2^(d-r)/4 : ℕ) : ℝ) ≤ rho*(2^d : ℕ) := by
    exact ((div_le_iff₀ hNpos).mp (hratio ▸ hquarterrho.le))
  have hK : 2^(d-r)/4 ≤ ⌊rho*(2^d : ℕ)⌋₊ :=
    (Nat.le_floor_iff (by positivity : 0 ≤ rho*(2^d : ℕ))).mpr hKreal
  have hJ : ⌊rho*(2^d : ℕ)⌋₊ ≤ 2^d :=
    Nat.floor_le_of_le (by nlinarith : rho*(2^d : ℕ) ≤ ((2^d : ℕ) : ℝ))
  have hJupper : (⌊rho*(2^d : ℕ)⌋₊ : ℝ) ≤ rho*(2^d : ℕ) :=
    Nat.floor_le (by positivity)
  have hout : (⌊rho*(2^d : ℕ)⌋₊ : ℝ) - ((2^(d-r)/4 : ℕ) : ℝ) ≤
      ((2^d : ℕ) : ℝ) - (2^(d-r) : ℕ) := by
    rw [←hratio] at hquartercomplement
    have hh := (div_lt_iff₀ hNpos).mp hquartercomplement
    rw [hquarter] at hh ⊢
    nlinarith
  refine ⟨hK, hJ, ?_, hMN⟩
  exact_mod_cast (show ((⌊rho*(2^d : ℕ)⌋₊-2^(d-r)/4 : ℕ) : ℝ) ≤
      ((2^d-2^(d-r) : ℕ) : ℝ) by
    rw [Nat.cast_sub hK, Nat.cast_sub hMN]
    exact hout)

/-- Integer padding preserves the limiting agreement with precisely the seed
deficit and a single floor loss; the matching upper bound has no error term. -/
theorem normalized_agreement_bounds (N M J T0 : ℕ) (rho delta : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (hquarterJ : M/4 ≤ J)
    (hquarter : ((M/4 : ℕ) : ℝ) = (M : ℝ)/4)
    (hdelta : 0 ≤ delta) (hseedlower : 1/2-(T0 : ℝ)/M ≤ delta)
    (hseedupper : (T0 : ℝ)/M ≤ 1/2)
    (hJlower : rho*N-1 ≤ (J : ℝ)) (hJupper : (J : ℝ) ≤ rho*N) :
    let T := J-M/4+T0
    rho+((M : ℝ)/N)/4-(delta+1/N) ≤ (T : ℝ)/N ∧
      (T : ℝ)/N ≤ rho+((M : ℝ)/N)/4 := by
  dsimp only
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hT : ((J-M/4+T0 : ℕ) : ℝ) = (J : ℝ)-(M : ℝ)/4+T0 := by
    rw [Nat.cast_add, Nat.cast_sub hquarterJ, hquarter]
  have hseedL : (M : ℝ)/2-M*delta ≤ T0 := by
    have hh := (le_div_iff₀ hMr).mp (show (1/2 : ℝ)-delta ≤ (T0 : ℝ)/M by linarith)
    linarith
  have hseedU : (T0 : ℝ) ≤ (M : ℝ)/2 := by
    have hh := (div_le_iff₀ hMr).mp hseedupper
    linarith
  have herr := mul_le_mul_of_nonneg_right hMNr hdelta
  constructor
  · apply (le_div_iff₀ hNr).mpr
    rw [hT]
    have heq : (rho+((M : ℝ)/N)/4-(delta+1/N))*(N : ℝ) =
        rho*N+(M : ℝ)/4-delta*N-1 := by field_simp; ring
    rw [heq]
    linarith
  · apply (div_le_iff₀ hNr).mpr
    rw [hT]
    have heq : (rho+((M : ℝ)/N)/4)*(N : ℝ) = rho*N+(M : ℝ)/4 := by
      field_simp
    rw [heq]
    linarith

/-- The seed deficit and the integer floor loss vanish as the full dimension
grows, with fixed seed codimension. -/
theorem all_rates_error_tendsto (C theta : ℝ) (htheta : 0 < theta) (r : ℕ) :
    Tendsto (fun d : ℕ => C * ((2^(d-r) : ℕ) : ℝ)^(-theta) +
      1/((2^d : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun d : ℕ => (2 : ℝ)^d) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hseed := ((tendsto_rpow_neg_atTop htheta).comp
    (hpow.comp (tendsto_sub_atTop_nat r))).const_mul C
  have hone := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_zero, mul_zero, zero_add, Function.comp_def]
    using hseed.add hone

end BinaryFieldCounterexamples.GoldAllRates
