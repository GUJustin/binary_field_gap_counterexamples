/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.HalfRateProbability
public import BinaryFieldCounterexamples.Counting.CollisionSimplifiedBound
/-!
# The sharp energy constant in the proofs of Corollary 6.7 and Theorem 6.10

The paper uses `NM²/8`, whereas the original asymptotic proofs only needed the
weaker `NM²/4`. These arithmetic lemmas prove the sharper constant, including
height two. Whole-tree populations are even because complementation is free.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- Corollary 6.7's proof: for an even population the balanced incidence
energy is at most `NM²/8` (the paper's sharper constant). -/
theorem whole_tree_energy_le_eighth (N K M : ℕ)
    (hK : (K : ℚ) ≤ N / 2) (heven : 2 ∣ M) :
    (K : ℚ) * M.choose 2 - (N : ℚ) * (M / 2).choose 2 ≤ (N : ℚ) * M ^ 2 / 8 := by
  have hhalf : ((M / 2 : ℕ) : ℚ) = (M : ℚ) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr
    exact_mod_cast Nat.div_mul_cancel heven
  rw [Nat.cast_choose_two ℚ, Nat.cast_choose_two ℚ, hhalf]
  have hchoose : 0 ≤ (M : ℚ) * ((M : ℚ) - 1) / 2 := by
    rw [← Nat.cast_choose_two ℚ]
    positivity
  have hm := mul_le_mul_of_nonneg_right hK hchoose
  nlinarith

/-- Theorem 6.10's proof: when `K=N/2` and `M≥1`, its literal avoiding-tree
energy is at most `NM²/8`. This includes the height-two remark. -/
theorem avoiding_tree_energy_le_eighth_of_half (N K w M : ℕ)
    (hN : 0 < N) (hK : (K : ℚ) = (N : ℚ) / 2)
    (hw : w < N) (hM : 1 ≤ M) :
    (((K : ℚ) - w - (K : ℚ)^2 / (N - w)) * M^2 + w*M) / 2 ≤
      (N : ℚ) * M^2 / 8 := by
  have hden : (0 : ℚ) < (N : ℚ) - w := by
    have h : (w : ℚ) < N := by exact_mod_cast hw
    linarith
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  have hMQ : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have hratio : (N : ℚ) / 4 ≤ (K : ℚ)^2 / (N - w) := by
    apply (le_div_iff₀ hden).mpr
    rw [hK]
    nlinarith [show (0 : ℚ) ≤ w by positivity]
  have hwm : (w : ℚ) * M ≤ (w : ℚ) * M^2 := by
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ w by positivity)
      (mul_nonneg (show (0 : ℚ) ≤ M by positivity) (sub_nonneg.mpr hMQ))]
  have hmul := mul_le_mul_of_nonneg_right hratio (sq_nonneg (M : ℚ))
  rw [hK] at hmul ⊢
  nlinarith

end BinaryFieldCounterexamples
