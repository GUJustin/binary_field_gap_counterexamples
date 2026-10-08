/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionAveraging
/-!
# Asymptotic consequence of a collision-energy bound

A second-moment image estimate gives a uniform constant fraction of the
smaller of the family size and the ambient field budget.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

set_option maxHeartbeats 500000

/-- A second-moment image bound is at least a constant times the smaller of
its family size and its ambient-field budget. -/
theorem one_third_min_le_of_second_moment
    (N M q Z : ℕ) (E : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hE0 : 0 ≤ E) (hE : E ≤ (N : ℚ) * M ^ 2 / 4)
    (hZ : ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤ Z) :
    (1 / 3 : ℚ) * min (M : ℚ) ((q : ℚ) / N) ≤ Z := by
  have hqN : N ≤ q := by omega
  have hx : (q : ℚ) / 2 ≤ (q - N : ℕ) := by
    rw [Nat.cast_sub hqN]
    have hqR : (2 : ℚ) * N ≤ q := by exact_mod_cast hq
    linarith
  have hx0 : (0 : ℚ) < (q - N : ℕ) := by
    exact_mod_cast (show 0 < q - N by omega)
  have hM0 : (0 : ℚ) < M := by exact_mod_cast hM
  have hden0 : (0 : ℚ) < (q - N : ℕ) * M + 2 * E := by positivity
  have hratio : (q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E) ≤ Z :=
    (Nat.ceil_le.mp hZ)
  let y : ℚ := (1 / 3) * min (M : ℚ) ((q : ℚ) / N)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyM : y ≤ (M : ℚ) / 3 := by
    dsimp [y]
    have := min_le_left (M : ℚ) ((q : ℚ) / N)
    linarith
  have hyq : y ≤ (q : ℚ) / (3 * N) := by
    dsimp [y]
    have := min_le_right (M : ℚ) ((q : ℚ) / N)
    have hNR : (0 : ℚ) < N := by exact_mod_cast hN
    field_simp at this ⊢
    linarith
  have hdenU : ((q - N : ℕ) : ℚ) * M + 2 * E ≤
      (q : ℚ) * M + (N : ℚ) * M ^ 2 / 2 := by
    have hxU : (((q - N : ℕ) : ℚ)) ≤ q := by
      exact_mod_cast Nat.sub_le q N
    nlinarith
  have htarget : y * (((q - N : ℕ) : ℚ) * M + 2 * E) ≤
      ((q - N : ℕ) : ℚ) * M ^ 2 := by
    have hleft : y * ((q : ℚ) * M + (N : ℚ) * M ^ 2 / 2) ≤
        (q : ℚ) * M ^ 2 / 2 := by
      have hNR : (0 : ℚ) < N := by exact_mod_cast hN
      have hqR : (0 : ℚ) ≤ q := by positivity
      have hpart1 : y * ((q : ℚ) * M) ≤ (q : ℚ) * M ^ 2 / 3 := by
        have hm := mul_le_mul_of_nonneg_right hyM (mul_nonneg hqR hM0.le)
        linarith
      have hpart2 : y * ((N : ℚ) * M ^ 2 / 2) ≤ (q : ℚ) * M ^ 2 / 6 := by
        calc
          _ ≤ ((q : ℚ) / (3 * N)) * ((N : ℚ) * M ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right hyq (by positivity)
          _ = _ := by field_simp; ring
      linarith
    have hright : (q : ℚ) * M ^ 2 / 2 ≤ ((q - N : ℕ) : ℚ) * M ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hx (sq_nonneg (M : ℚ))]
    exact (mul_le_mul_of_nonneg_left hdenU hy0).trans hleft |>.trans hright
  have hy : y ≤ (q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E) :=
    by
      rw [show (q - N : ℚ) = ((q - N : ℕ) : ℚ) by rw [Nat.cast_sub hqN]]
      exact (le_div_iff₀ hden0).2 htarget
  exact hy.trans hratio

/-- Real-valued form of `one_third_min_le_of_second_moment`, for direct use
in the asymptotic statements. -/
theorem one_third_min_real_le_of_second_moment
    (N M q Z : ℕ) (E : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hE0 : 0 ≤ E) (hE : E ≤ (N : ℚ) * M ^ 2 / 4)
    (hZ : ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤ Z) :
    (1 / 3 : ℝ) * min (M : ℝ) ((q : ℝ) / N) ≤ Z := by
  have h := one_third_min_le_of_second_moment N M q Z E hN hM hq hE0 hE hZ
  have hc := (Rat.cast_le (K := ℝ)).2 h
  norm_num [Rat.cast_div] at hc
  simpa only [Nat.cast_ofNat, Nat.cast_min] using hc

end BinaryFieldCounterexamples
