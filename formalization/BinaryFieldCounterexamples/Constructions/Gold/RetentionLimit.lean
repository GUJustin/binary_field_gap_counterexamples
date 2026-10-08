/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.ExactRetentionProbability
public import BinaryFieldCounterexamples.Constructions.Gold.DenseParameters
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Padding retention tends to one

The probability in Lemma 5.14 (`lem:locator-padding`, p. 46) is at least
`1 - 2^(r-s)` for `r ≤ s < d`.  Here the negative exponent is written exactly
as `(1/2)^(s-r)`.  Its half-rate specialization is the estimate in the proof
of Corollary 5.15 (`cor:gold-half-rate`, p. 46).

For every rank parameter bounded by `d/4`, the half-rate retention tends to
one as `d` tends to infinity.  In particular this applies to the explicit
`denseT` choice of Corollary 5.2 (`cor:gold-dense-domains`, p. 37).
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
open Filter

/-- The finite numerator product has the geometric union-bound lower estimate,
including its positive remainder. -/
theorem binary_padding_numerator_lower (s r : ℕ) (hrs : r ≤ s) :
    1 - (1/2:ℚ)^(s-r) + (1/2:ℚ)^s ≤
      ∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(s-i)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr : r ≤ s := by omega
    have he : (1/2:ℚ)^(s-r) = (1/2:ℚ)^(s-(r+1))/2 := by
      rw [show s-r = (s-(r+1))+1 by omega, pow_succ]
      ring
    have hp : (1/2:ℚ)^(s-r) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_right (ih hr) (sub_nonneg.mpr hp)
    rw [Finset.prod_range_succ]
    have hn : 0 ≤ (1/2:ℚ)^(s-r) := by positivity
    have hs : (1/2:ℚ)^s ≤ (1/2:ℚ)^(s-r) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hs)]

/-- The exact success probability from Lemma 5.14 is at least `1 - 2^(r-s)`.
The result also includes the harmless boundary `s = d`. -/
theorem paddingRetentionProbability_lower (d s r : ℕ) (hrs : r ≤ s) (hsd : s ≤ d) :
    1 - (1/2:ℚ)^(s-r) ≤ paddingRetentionProbability d s r := by
  rw [paddingRetentionProbability_product d s r hrs hsd]
  have hprod : (∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(s-i))) ≤
      ∏ i ∈ Finset.range r, (1-(1/2:ℚ)^(s-i))/(1-(1/2:ℚ)^(d-i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
    · intro i hi
      have hir := Finset.mem_range.mp hi
      have hd : (1/2:ℚ)^(d-i) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have hs : (1/2:ℚ)^(s-i) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      apply (le_div_iff₀ (sub_pos.mpr hd)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hs)
        (show 0 ≤ (1/2:ℚ)^(d-i) by positivity)]
  have hn := binary_padding_numerator_lower s r hrs
  have hs : 0 ≤ (1/2:ℚ)^s := by positivity
  linarith

/-- Each spanning factor is at most one, so the exact retention is a probability. -/
theorem paddingRetentionProbability_le_one (d s r : ℕ) (hrs : r ≤ s) (hsd : s ≤ d) :
    paddingRetentionProbability d s r ≤ 1 := by
  rw [paddingRetentionProbability_product d s r hrs hsd]
  calc
    _ ≤ ∏ _i ∈ Finset.range r, (1:ℚ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hir := Finset.mem_range.mp hi
        have hd : (1/2:ℚ)^(d-i) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))
          (sub_pos.mpr hd).le
      · intro i hi
        have hir := Finset.mem_range.mp hi
        have hd : (1/2:ℚ)^(d-i) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        apply (div_le_one (sub_pos.mpr hd)).mpr
        have hp : (1/2:ℚ)^(d-i) ≤ (1/2:ℚ)^(s-i) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
    _ = 1 := by simp

/-- The bound `p_{d,d-2,2t} ≥ 1 - 2^(2t+2-d)` in Corollary 5.15's proof. -/
theorem paddingRetentionProbability_half_rate_lower (d t : ℕ) (hd : 2 ≤ d)
    (ht : 2*t ≤ d-2) :
    1 - (1/2:ℚ)^(d-(2*t+2)) ≤ paddingRetentionProbability d (d-2) (2*t) := by
  simpa [Nat.sub_sub, Nat.add_comm] using
    paddingRetentionProbability_lower d (d-2) (2*t) ht (by omega)

/-- Any half-rate rank choice eventually bounded by `d/4` has retention tending
to one.  Small, inadmissible dimensions do not affect the limit. -/
theorem paddingRetentionProbability_half_rate_tendsto (t : ℕ → ℕ)
    (ht : ∀ᶠ d in atTop, t d ≤ d/4) :
    Tendsto (fun d => (paddingRetentionProbability d (d-2) (2*t d) : ℝ))
      atTop (nhds 1) := by
  -- The exponent in the finite error bound tends to infinity.
  have hexp : Tendsto (fun d => d-(2*t d+2)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [ht, eventually_ge_atTop (2*k+4)] with d htd hd
    omega
  have hpow : Tendsto (fun d => (1/2:ℝ)^(d-(2*t d+2))) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).comp hexp
  have hlower : Tendsto (fun d => 1-(1/2:ℝ)^(d-(2*t d+2))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hpow
  -- Squeeze the exact rational probability between its lower bound and one.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [ht, eventually_ge_atTop 4] with d htd hd
    have hr : 2*t d ≤ d-2 := by omega
    have h := paddingRetentionProbability_half_rate_lower d (t d) (by omega) hr
    have hreal := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hreal
  · filter_upwards [ht, eventually_ge_atTop 4] with d htd hd
    have hr : 2*t d ≤ d-2 := by omega
    exact_mod_cast paddingRetentionProbability_le_one d (d-2) (2*t d) hr (by omega)

namespace Gold

/-- For the parameter `t = min (⌊d/4⌋) (⌊(d+c-1)/(c+1)⌋)` in Corollary 5.2,
the half-rate padding proportion is `1-o(1)`, as asserted in Corollary 5.15. -/
theorem denseGold_paddingRetentionProbability_tendsto (c : ℕ) :
    Tendsto (fun d => (paddingRetentionProbability d (d-2) (2*denseT c d) : ℝ))
      atTop (nhds 1) := by
  exact paddingRetentionProbability_half_rate_tendsto (denseT c)
    (Eventually.of_forall (denseT_le_quarter c))

end Gold

end BinaryFieldCounterexamples
