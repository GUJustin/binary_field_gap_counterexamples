/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics

/-!
# Main theorem companion: every interior rate is covered

The open interval in Corollary 5.24, p. 56 contains each fixed rate strictly
between zero and one for a sufficiently large fixed binary power. This numeric
coverage assertion is proved independently of the proved dense construction
in `DenseAllRates.lean`. The exponent is chosen after the rate and fixed offset,
not after a growing code length.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
/-- Every fixed interior rate belongs to the dense construction's open interval
for a sufficiently large fixed binary power. -/
theorem dense_all_rates_rate_coverage (c : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ' : ρ < 1) :
    ∃ k : ℕ, c < k ∧
      (2 : ℝ) ^ c / ((2 : ℝ) ^ k) ^ 2 < ρ ∧
      ρ < 1 - (2 : ℝ) ^ c / (2 : ℝ) ^ k +
        (2 : ℝ) ^ c / ((2 : ℝ) ^ k) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max ((2 : ℝ)^c / ρ) ((2 : ℝ)^c / (1-ρ)))
  have hn : max ((2 : ℝ)^c / ρ) ((2 : ℝ)^c / (1-ρ)) < (2 : ℝ)^n :=
    hn.trans (by exact_mod_cast n.lt_two_pow_self)
  let k := n + c + 1
  have hk : c < k := by dsimp [k]; omega
  have hnk : (2 : ℝ)^n ≤ 2^k := pow_le_pow_right₀ (by norm_num) (by dsimp [k]; omega)
  have hpos : 0 < (2 : ℝ)^k := by positivity
  have hpow : 1 ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hsmall : (2 : ℝ)^c / 2^k < ρ := by
    apply (div_lt_iff₀ hpos).mpr
    have h := (div_lt_iff₀ hρ).mp ((le_max_left _ _).trans_lt (hn.trans_le hnk))
    linarith
  have hsmall' : (2 : ℝ)^c / 2^k < 1-ρ := by
    apply (div_lt_iff₀ hpos).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hρ')).mp
      ((le_max_right _ _).trans_lt (hn.trans_le hnk))
    linarith
  refine ⟨k, hk, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hsmall
    apply div_le_div_of_nonneg_left (by positivity) hpos
    nlinarith
  · have : 0 < (2 : ℝ)^c / ((2 : ℝ)^k)^2 := by positivity
    linarith
end BinaryFieldCounterexamples
