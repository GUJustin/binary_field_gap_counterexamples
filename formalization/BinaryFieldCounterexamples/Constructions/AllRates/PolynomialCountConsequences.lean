/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial count consequences of Theorem 4.5

The probability estimate becomes a polynomial lower bound when the challenge
field (or the intermediate field in part 3) has at least `N^s` elements.
The explicit constant and large-length condition also remove the additive loss
of one challenge, giving the asserted Omega lower bound.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- Theorem 4.5, parts 1 and 3: a field of size at least `N^s` makes the
rational count bound at least `N^s/(1+C)-1`. -/
theorem all_rates_count_lower_bound (x q C b : ℝ)
    (hx : 0 < x) (hq : x ≤ q) (hC : 0 < C)
    (hb : q / (1 + C * q / x) - 1 ≤ b) :
    x / (1 + C) - 1 ≤ b := by
  have hqpos : 0 < q := hx.trans_le hq
  have hden : 0 < 1 + C * q / x := by positivity
  have hbase : x / (1 + C) ≤ q / (1 + C * q / x) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    field_simp
    nlinarith
  linarith

/-- Theorem 4.5 part 1, in particular: its actual exceptional set has at
least `N^s/(1+C)-1` nonzero challenges whenever `q ≥ N^s`. -/
theorem all_rates_nonzero_count_of_probability
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset F) (J T s : ℕ) (f g : D → F) (C : ℝ)
    (hN : 0 < D.card) (hC : 0 < C)
    (hq : (D.card : ℝ)^s ≤ Fintype.card F)
    (hp : 1 / (1 + C * Fintype.card F / (D.card : ℝ)^s) -
      1 / Fintype.card F ≤
      ((nonzeroBadChallenges D J f g T).card : ℝ) / Fintype.card F) :
    (D.card : ℝ)^s / (1 + C) - 1 ≤
      (nonzeroBadChallenges D J f g T).card := by
  have hqpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmul := (mul_le_mul_of_nonneg_right hp hqpos.le)
  have hbound : (Fintype.card F : ℝ) /
      (1 + C * Fintype.card F / (D.card : ℝ)^s) - 1 ≤
      (nonzeroBadChallenges D J f g T).card := by
    field_simp at hmul ⊢
    nlinarith
  exact all_rates_count_lower_bound _ _ _ _
    (pow_pos (by exact_mod_cast hN) _) hq hC hbound

/-- Theorem 4.5's Omega consequence, including the `s=2` quadratic count:
for large `N`, the explicit count bound is at least `N^s/(2(1+C))`. -/
theorem all_rates_omega_from_count (x C b : ℝ) (hC : 0 < C)
    (hlarge : 2 * (1 + C) ≤ x) (hb : x / (1 + C) - 1 ≤ b) :
    x / (2 * (1 + C)) ≤ b := by
  have hden : 0 < 1 + C := by positivity
  have hr : 2 ≤ x / (1 + C) := (le_div_iff₀ hden).mpr hlarge
  have he : x / (2 * (1 + C)) = (x / (1 + C)) / 2 := by field_simp
  rw [he]
  linarith

end BinaryFieldCounterexamples
