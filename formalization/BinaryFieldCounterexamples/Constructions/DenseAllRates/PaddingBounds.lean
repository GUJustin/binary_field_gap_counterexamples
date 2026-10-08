/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Normalized dense-padding bounds

The inclusion-exclusion expression produced by balanced nodal padding has the
paper's exact density `α`.  These lemmas isolate the finite rounding, initial
agreement deficit, and balanced-overlap error for later asymptotic assembly.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- The normalized union bound behind dense all-rate padding.  Here `x` is the
padding density and `τ` is the old agreement density. -/
theorem normalized_balanced_padding_lower
    (a b ρ ε η x τ : ℝ)
    (hb : 1 ≤ b) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : ρ - a / b ^ 2 - η ≤ x)
    (hτ : 1 / b - ε ≤ τ) :
    1 / b + (ρ - a / b ^ 2) * (1 - 1 / b) - ε - η ≤
      x + τ - x * τ := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hc0 : 0 ≤ 1 - 1 / b := by
    have : 1 / b ≤ 1 := (div_le_one hbpos).2 hb
    linarith
  have hc1 : 1 - 1 / b ≤ 1 := by
    have : 0 ≤ 1 / b := div_nonneg zero_le_one hbpos.le
    linarith
  have hprod : (1 - x) * (1 / b - ε) ≤ (1 - x) * τ :=
    mul_le_mul_of_nonneg_left hτ (sub_nonneg.mpr hx1)
  have hxprod : (ρ - a / b ^ 2 - η) * (1 - 1 / b) ≤
      x * (1 - 1 / b) := mul_le_mul_of_nonneg_right hx hc0
  have hεprod : ε * (1 - x) ≤ ε := by nlinarith
  have hηprod : η * (1 - 1 / b) ≤ η :=
    mul_le_of_le_one_right hη hc1
  linarith

/-- Exact normalization of the inclusion-exclusion expression used after
balanced padding. -/
theorem normalized_padding_union_identity
    (N w T Δ : ℝ) (hN : 0 < N) :
    (w + T - w * T / N - Δ) / N =
      w / N + T / N - (w / N) * (T / N) - Δ / N := by
  field_simp

/-- Finite normalized form: any lower bounds on the padding and old-agreement
densities transfer directly to the padded union density, with the balanced
intersection error divided by the domain size. -/
theorem dense_balanced_padding_fraction_lower
    (a b ρ ε η N w T Δ : ℝ)
    (hb : 1 ≤ b) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hN : 0 < N)
    (hw0 : 0 ≤ w) (hwN : w ≤ N)
    (hw : ρ - a / b ^ 2 - η ≤ w / N)
    (hT : 1 / b - ε ≤ T / N) :
    1 / b + (ρ - a / b ^ 2) * (1 - 1 / b) - ε - η - Δ / N ≤
      (w + T - w * T / N - Δ) / N := by
  have hx0 : 0 ≤ w / N := div_nonneg hw0 hN.le
  have hx1 : w / N ≤ 1 := (div_le_one hN).2 hwN
  have hbase := normalized_balanced_padding_lower a b ρ ε η
    (w / N) (T / N) hb hε hη hx0 hx1 hw hT
  rw [normalized_padding_union_identity N w T Δ hN]
  linarith

end BinaryFieldCounterexamples
