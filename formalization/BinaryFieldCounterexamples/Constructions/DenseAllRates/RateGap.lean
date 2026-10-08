/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
/-!
# Strict dense agreement fraction bounds

The open rate interval places the prescribed agreement fraction strictly
between the rate and its Johnson square root.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- The original open interval gives both strict agreement-fraction inequalities. -/
theorem dense_agreement_fraction_gap (a b ρ : ℝ) (ha : 1≤a) (hb : 1<b)
    (hlo : a/b^2<ρ) (hhi : ρ<1-a/b+a/b^2) :
    ρ<1/b+(ρ-a/b^2)*(1-1/b) ∧
      1/b+(ρ-a/b^2)*(1-1/b)<Real.sqrt ρ := by
  have hb0 : 0<b := by linarith
  have hu : 0<1/b := by positivity
  have hu1 : 1/b<1 := (div_lt_one hb0).mpr hb
  have ha0 : 0<a := by linarith
  have hρ0 : 0<ρ := lt_trans (by positivity) hlo
  have hρ1 : ρ<1 := by
    have hh : a/b^2<a/b := by
      apply div_lt_div_of_pos_left ha0 hb0
      nlinarith
    linarith
  have hs : (Real.sqrt ρ)^2=ρ := Real.sq_sqrt hρ0.le
  have hz : 0≤Real.sqrt ρ := Real.sqrt_nonneg _
  have hz1 : Real.sqrt ρ<1 := by nlinarith
  have hlow : (1/b)^2<ρ := by
    have hh : 1/b^2≤a/b^2 := div_le_div_of_nonneg_right ha (by positivity)
    simpa only [div_pow,one_pow] using hh.trans_lt hlo
  have huz : 1/b<Real.sqrt ρ := by nlinarith
  constructor
  · have he : (1/b+(ρ-a/b^2)*(1-1/b)-ρ)*b=1-a/b+a/b^2-ρ := by field_simp; ring
    nlinarith
  · have hbound : 1/b+(ρ-a/b^2)*(1-1/b)≤1/b+(ρ-(1/b)^2)*(1-1/b) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      have hh : 1/b^2≤a/b^2 := div_le_div_of_nonneg_right ha (by positivity)
      simpa only [div_pow,one_pow] using sub_le_sub_left hh ρ
    apply hbound.trans_lt
    have hprod := mul_pos (sub_pos.mpr huz)
      (show 0<(1-1/b)*(1-Real.sqrt ρ)+(1/b)^2 by positivity)
    nlinarith
end BinaryFieldCounterexamples
