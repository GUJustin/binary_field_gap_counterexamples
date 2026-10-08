/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.RationalCollision
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# The simplified flats-to-challenges collision bound

Step 4 of Lemma 6.1 (Unions of flats give exceptional challenges), p. 59,
of the paper proves that an energy budget `F ≤ N M² / 8` gives
`Z(M,F) ≥ min {M/2, q/N}`. The second-moment term alone gives this bound.
The numerical result below needs only `q ≥ 2N`; powers of two with `q > N`
are a sufficient condition rather than an additional restriction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- The numerical estimate behind Step 4, over any ordered field. -/
theorem half_or_field_min_le_second_moment_of_orderedField
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (N M q F : α) (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ N * M ^ 2 / 8) :
    min (M / 2) (q / N) ≤ (q - N) * M ^ 2 / ((q - N) * M + 2 * F) := by
  have hx : 0 < q - N := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hden : 0 < (q - N) * M + 2 * F := by positivity
  let y := min (M / 2) (q / N)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyM : y ≤ M / 2 := min_le_left _ _
  have hyq : y * N ≤ 2 * (q - N) := by
    have hmin : y ≤ q / N := min_le_right _ _
    have hmul := (le_div_iff₀ hN).mp hmin
    linarith

  -- Split the denominator into its diagonal and collision contributions.
  have hdiag : y * ((q - N) * M) ≤ (q - N) * M ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hyM (mul_nonneg hx.le hM.le)
    nlinarith
  have henergy : y * (2 * F) ≤ (q - N) * M ^ 2 / 2 := by
    have hfirst := mul_le_mul_of_nonneg_left hF hy0
    have hsecond := mul_le_mul_of_nonneg_right hyq (sq_nonneg M)
    nlinarith
  apply (le_div_iff₀ hden).mpr
  change y * ((q - N) * M + 2 * F) ≤ _
  nlinarith

/-- The exact rational second-moment expression in Lemma 6.1 is at least
`min {M/2, q/N}` when the collision energy is at most `N M² / 8`.
The variables count the domain, the support family and the field respectively;
the energy itself is allowed to be an arbitrary nonnegative rational. -/
theorem half_or_field_min_le_second_moment
    (N M q : ℕ) (F : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ (N : ℚ) * M ^ 2 / 8) :
    min ((M : ℚ) / 2) ((q : ℚ) / N) ≤
      (q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * F) := by
  exact half_or_field_min_le_second_moment_of_orderedField (N : ℚ) M q F
    (by exact_mod_cast hN) (by exact_mod_cast hM) (by exact_mod_cast hq) hF0 hF

/-- Any natural challenge count bounded below by the paper's second-moment
ceiling satisfies the sharp simplified bound in Lemma 6.1. -/
theorem half_or_field_min_le_of_second_moment
    (N M q Z : ℕ) (F : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ (N : ℚ) * M ^ 2 / 8)
    (hZ : ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * F)⌉₊ ≤ Z) :
    min ((M : ℚ) / 2) ((q : ℚ) / N) ≤ Z := by
  exact (half_or_field_min_le_second_moment N M q F hN hM hq hF0 hF).trans
    (Nat.ceil_le.mp hZ)

/-- The literal `Z(M,F)` max of Lemma 6.1, with the same floor and ceiling,
satisfies its printed simplified bound. -/
theorem half_or_field_min_le_collision_bound
    (N M q : ℕ) (F : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ (N : ℚ) * M ^ 2 / 8) :
    min ((M : ℚ) / 2) ((q : ℚ) / N) ≤
      (max (M - ⌊F / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * F)⌉₊ : ℕ) := by
  apply half_or_field_min_le_of_second_moment N M q _ F hN hM hq hF0 hF
  exact le_max_right _ _

/-- Real-valued form of the simplified bound, for tree asymptotics. -/
theorem half_or_field_min_real_le_of_second_moment
    (N M q Z : ℕ) (F : ℚ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ (N : ℚ) * M ^ 2 / 8)
    (hZ : ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * F)⌉₊ ≤ Z) :
    min ((M : ℝ) / 2) ((q : ℝ) / N) ≤ Z := by
  have h := half_or_field_min_le_of_second_moment N M q Z F hN hM hq hF0 hF hZ
  have hc := (Rat.cast_le (K := ℝ)).2 h
  norm_num [Rat.cast_div] at hc
  simpa only [min_le_iff] using hc

/-- The precise powers-of-two regime in Step 4 of Lemma 6.1 gives the
numerical hypothesis `q ≥ 2N` without any extra field-size assumption. -/
theorem two_mul_le_of_binary_powers_lt (d r : ℕ)
    (h : 2 ^ d < 2 ^ r) : 2 * 2 ^ d ≤ 2 ^ r := by
  have hdr : d < r := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h
  calc
    2 * 2 ^ d = 2 ^ (d + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)

/-- The paper's literal collision max has the stated lower bound when both
the domain and field sizes are powers of two and the field is larger. -/
theorem half_or_field_min_le_collision_bound_binary
    (d r M : ℕ) (F : ℚ)
    (hM : 0 < M) (hq : 2 ^ d < 2 ^ r)
    (hF0 : 0 ≤ F) (hF : F ≤ (2 ^ d : ℚ) * M ^ 2 / 8) :
    min ((M : ℚ) / 2) ((2 ^ r : ℚ) / 2 ^ d) ≤
      (max (M - ⌊F / (2 ^ r - 2 ^ d)⌋₊)
        ⌈(2 ^ r - 2 ^ d : ℚ) * M ^ 2 /
          ((2 ^ r - 2 ^ d) * M + 2 * F)⌉₊ : ℕ) := by
  have hF' : F ≤ ((2 ^ d : ℕ) : ℚ) * M ^ 2 / 8 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hF
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    half_or_field_min_le_collision_bound (2 ^ d) M (2 ^ r) F
      (by positivity) hM (two_mul_le_of_binary_powers_lt d r hq) hF0 hF'

/-- Enlarging a rational collision budget to an arbitrary real budget can
only decrease both terms of the exact `Z(M,F)` bound. This lets rational
finite collision counts establish the paper's arbitrary real-budget statement. -/
theorem real_collision_bound_le_rat_of_budget_le
    (N M q : ℕ) (E : ℚ) (F : ℝ)
    (hM : 0 < M) (hq : N < q) (hE : 0 ≤ E) (hEF : (E : ℝ) ≤ F) :
    max (M - ⌊F / (q - N)⌋₊)
        ⌈(q - N : ℝ) * M ^ 2 / ((q - N) * M + 2 * F)⌉₊ ≤
      max (M - ⌊E / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ := by
  have hqR : (N : ℝ) < q := by exact_mod_cast hq
  have hx : (0 : ℝ) < q - N := by linarith
  have hqQ : (N : ℚ) < q := by exact_mod_cast hq
  have hxQ : (0 : ℚ) < q - N := by linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hER : (0 : ℝ) ≤ E := by exact_mod_cast hE
  have hden : (0 : ℝ) < (q - N) * M + 2 * (E : ℝ) := by positivity
  apply max_le_max
  · have hfloor : ⌊E / (q - N)⌋₊ ≤ ⌊F / (q - N)⌋₊ := by
      apply Nat.le_floor
      have hrat : (⌊E / (q - N)⌋₊ : ℚ) ≤ E / (q - N) :=
        Nat.floor_le (by positivity)
      have hcast := (Rat.cast_le (K := ℝ)).mpr hrat
      simp only [Rat.cast_natCast, Rat.cast_div, Rat.cast_sub] at hcast
      exact hcast.trans (div_le_div_of_nonneg_right hEF hx.le)
    omega
  · apply Nat.ceil_le.mpr
    have hrat : (q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E) ≤
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ := Nat.le_ceil _
    have hcast := (Rat.cast_le (K := ℝ)).mpr hrat
    simp only [Rat.cast_natCast, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at hcast
    apply le_trans _ hcast
    apply div_le_div_of_nonneg_left (by positivity) hden
    linarith

/-- The printed simplified bound with an arbitrary nonnegative real energy.
No rationality restriction is imposed on the paper's budget. -/
theorem half_or_field_min_le_collision_bound_real
    (N M q : ℕ) (F : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hq : 2 * N ≤ q)
    (hF0 : 0 ≤ F) (hF : F ≤ (N : ℝ) * M ^ 2 / 8) :
    min ((M : ℝ) / 2) ((q : ℝ) / N) ≤
      (max (M - ⌊F / (q - N)⌋₊)
        ⌈(q - N : ℝ) * M ^ 2 / ((q - N) * M + 2 * F)⌉₊ : ℕ) := by
  have h := half_or_field_min_le_second_moment_of_orderedField (N : ℝ) M q F
    (by exact_mod_cast hN) (by exact_mod_cast hM) (by exact_mod_cast hq) hF0 hF
  exact h.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _)))

/-- The full powers-of-two form of Step 4, including an arbitrary real
energy budget rather than only a rational budget. -/
theorem half_or_field_min_le_collision_bound_binary_real
    (d r M : ℕ) (F : ℝ)
    (hM : 0 < M) (hq : 2 ^ d < 2 ^ r)
    (hF0 : 0 ≤ F) (hF : F ≤ (2 ^ d : ℝ) * M ^ 2 / 8) :
    min ((M : ℝ) / 2) ((2 ^ r : ℝ) / 2 ^ d) ≤
      (max (M - ⌊F / (2 ^ r - 2 ^ d)⌋₊)
        ⌈(2 ^ r - 2 ^ d : ℝ) * M ^ 2 /
          ((2 ^ r - 2 ^ d) * M + 2 * F)⌉₊ : ℕ) := by
  have hF' : F ≤ ((2 ^ d : ℕ) : ℝ) * M ^ 2 / 8 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hF
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    half_or_field_min_le_collision_bound_real (2 ^ d) M (2 ^ r) F
      (by positivity) hM (two_mul_le_of_binary_powers_lt d r hq) hF0 hF'

end BinaryFieldCounterexamples
