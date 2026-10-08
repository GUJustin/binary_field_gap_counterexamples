/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Quantitative error bounds for the dense construction

These estimates convert the finite Gaussian population and middle-rank
denominators into the logarithmic growth and fourth-root bounds used by the
dense all-rate theorem.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- An upper binary-power bound gives the corresponding logarithmic bound. -/
theorem log_two_mul_nat_le_of_le_two_pow (L E : ℕ) (hL : 0 < L)
    (hLE : L ≤ 2 ^ E) :
    Real.log (2 * L) ≤ (E + 1 : ℕ) * Real.log 2 := by
  have hcast : (2 * L : ℝ) ≤ (2 ^ (E + 1) : ℕ) := by
    exact_mod_cast (show 2 * L ≤ 2 ^ (E + 1) by
      rw [pow_succ]
      omega)
  have hpos : (0 : ℝ) < 2 * L := by positivity
  calc
    Real.log (2 * L) ≤ Real.log ((2 ^ (E + 1) : ℕ)) :=
      Real.log_le_log hpos hcast
    _ = (E + 1 : ℕ) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
      norm_num

/-- The middle-rank denominator has fourth power at least the full binary
ambient size.  This is the elementary source of the `N^(-1/4)` rank error. -/
theorem dense_rank_denominator_fourth (k n : ℕ) :
    2 ^ (2 * k * n) ≤ ((2 ^ k) ^ (n / 2 + 1)) ^ 4 := by
  have hn : 2 * n ≤ 4 * (n / 2 + 1) := by omega
  have he : 2 * k * n ≤ k * ((n / 2 + 1) * 4) := by
    have := Nat.mul_le_mul_left k hn
    linarith
  calc
    2 ^ (2 * k * n) ≤ 2 ^ (k * ((n / 2 + 1) * 4)) :=
      Nat.pow_le_pow_right (by decide) he
    _ = ((2 ^ k) ^ (n / 2 + 1)) ^ 4 := by rw [pow_mul, pow_mul]

/-- The same fourth-power comparison after deleting a fixed binary
codimension from the domain exponent. -/
theorem dense_rank_denominator_fourth_codim (k n c : ℕ) :
    2 ^ (2 * k * n - c) ≤ ((2 ^ k) ^ (n / 2 + 1)) ^ 4 := by
  exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans
    (dense_rank_denominator_fourth k n)

/-- Concrete logarithmic control for the actual middle-rank dense population. -/
theorem denseQuadraticListCount_binary_half_log_bound (k n : ℕ)
    (hk : 0 < k) (hn : 2 ≤ n) :
    Real.log (2 * denseQuadraticListCount (2 ^ k) n (n / 2)) ≤
      (n + k * (4 * n ^ 2 + 2) + 1 : ℕ) * Real.log 2 := by
  have hb := denseQuadraticListCount_binary_half_bounds k n hk hn
  have hpos : 0 < denseQuadraticListCount (2 ^ k) n (n / 2) := by
    have : 0 < 2 ^ (2 * k * (n / 2) ^ 2) := pow_pos (by decide) _
    omega
  exact log_two_mul_nat_le_of_le_two_pow _ _ hpos hb.2

/-- A pointwise square budget controls the normalized balanced-padding
fluctuation. -/
theorem balancedDeviation_div_le (N w I : ℕ) (δ : ℝ)
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hbudget : ((w : ℝ) / 2) * Real.log (2 * I) ≤ (δ * N) ^ 2) :
    Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I)) / N ≤ δ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hNR).2
  exact (Real.sqrt_le_iff).2 ⟨mul_nonneg hδ hNR.le, hbudget⟩

/-- A binary population with the middle-rank quadratic exponent is
superpolynomial in a binary domain of exponent at most `2kn`. -/
theorem binary_middle_rank_population_superpolynomial
    (k n c N L : ℕ) (hk : 0 < k) (hn : 4 ≤ n)
    (hN : N = 2 ^ (2 * k * n - c))
    (hL : 2 ^ (2 * k * (n / 2) ^ 2) ≤ L) :
    (N : ℝ) ^ ((1 / (32 * k : ℝ)) * Real.log N) ≤ L := by
  let D := 2 * k * n - c
  let t := n / 2
  let E := 2 * k * t ^ 2
  have ht : 0 < t := by dsimp [t]; omega
  have hDpos : 0 < (2 : ℝ) ^ D := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hnt : n ≤ 4 * t := by dsimp [t]; omega
  have hDle : D ≤ 8 * k * t := by
    calc
      D ≤ 2 * k * n := Nat.sub_le _ _
      _ ≤ 2 * k * (4 * t) := Nat.mul_le_mul_left (2 * k) hnt
      _ = 8 * k * t := by ring
  have hsq : D ^ 2 ≤ 32 * k * E := by
    dsimp [E]
    linarith [(sq_le_sq₀ (Nat.zero_le D) (Nat.zero_le (8 * k * t))).2 hDle]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqR : (D : ℝ) ^ 2 ≤ 32 * k * E := by exact_mod_cast hsq
  have hexp :
      (1 / (32 * k : ℝ)) * ((D : ℝ) * Real.log 2) ^ 2 ≤
        (E : ℝ) * Real.log 2 := by
    have hlog0 : 0 ≤ Real.log 2 := hlog2pos.le
    have hlogsq : (Real.log 2) ^ 2 ≤ Real.log 2 := by nlinarith
    have hD0 : 0 ≤ (D : ℝ) ^ 2 := sq_nonneg _
    have h₁ := mul_le_mul_of_nonneg_left hlogsq hD0
    have h₂ := mul_le_mul_of_nonneg_right hsqR hlog0
    field_simp
    nlinarith
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hlogN : Real.log (N : ℝ) = (D : ℝ) * Real.log 2 := by
    rw [hN]
    push_cast
    exact Real.log_pow 2 D
  have hpowL : ((2 ^ E : ℕ) : ℝ) ≤ L := by
    exact_mod_cast hL
  calc
    (N : ℝ) ^ ((1 / (32 * k : ℝ)) * Real.log N) =
        Real.exp ((1 / (32 * k : ℝ)) * (Real.log N) ^ 2) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      ring
    _ ≤ Real.exp ((E : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by simpa [hlogN] using hexp)
    _ = ((2 ^ E : ℕ) : ℝ) := by
      rw [← Real.log_pow]
      push_cast
      rw [Real.exp_log]
      positivity
    _ ≤ L := hpowL
/-- A binary exponential with quadratic exponent is bounded by a fixed
`N^(C log N)` once the binary domain exponent dominates the dimension. -/
theorem binary_quadratic_exponent_field_upper
    (k n c N F : ℕ) (hk : 0 < k) (hn : max 2 c ≤ n)
    (hN : N = 2 ^ (2 * k * n - c))
    (hF : F ≤ 2 ^ (n + k * (4 * n ^ 2 + 2))) :
    (F : ℝ) ≤ (N : ℝ) ^
      (((8 * k + 3 : ℕ) : ℝ) / Real.log 2 * Real.log N) := by
  let D := 2 * k * n - c
  let U := n + k * (4 * n ^ 2 + 2)
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hcn : c ≤ n := (le_max_right _ _).trans hn
  have hkn : n ≤ k * n := by nlinarith
  have hDlower : n ≤ D := by
    dsimp [D]
    have htwo : 2 * n ≤ 2 * k * n := by linarith
    omega
  have hU : U ≤ (8 * k + 3) * D ^ 2 := by
    dsimp [U]
    have hn_sq : n ≤ n ^ 2 := by nlinarith
    have hDsq := (sq_le_sq₀ (Nat.zero_le n) (Nat.zero_le D)).2 hDlower
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hlogN : Real.log (N : ℝ) = (D : ℝ) * Real.log 2 := by
    rw [hN]
    push_cast
    exact Real.log_pow 2 D
  have hFR : (F : ℝ) ≤ ((2 ^ U : ℕ) : ℝ) := by exact_mod_cast hF
  have hUR : (U : ℝ) ≤ (8 * k + 3 : ℕ) * (D : ℝ) ^ 2 := by
    exact_mod_cast hU
  calc
    (F : ℝ) ≤ ((2 ^ U : ℕ) : ℝ) := hFR
    _ = Real.exp ((U : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      push_cast
      rw [Real.exp_log]
      positivity
    _ ≤ Real.exp (((8 * k + 3 : ℕ) : ℝ) * (D : ℝ) ^ 2 * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hUR hlog2pos.le
    _ = (N : ℝ) ^ (((8 * k + 3 : ℕ) : ℝ) / Real.log 2 * Real.log N) := by
      rw [Real.rpow_def_of_pos hNpos, hlogN]
      congr 1
      field_simp


/-- A coarse explicit domination of a square by a half-speed binary exponential. -/
theorem nat_square_le_thirtyTwo_mul_two_pow_half (n : ℕ) :
    n ^ 2 ≤ 32 * 2 ^ (n / 2) := by
  let r := n / 4 + 1
  have hnr : n ≤ 4 * r := by dsimp [r]; omega
  have hsq := (sq_le_sq₀ (Nat.zero_le n) (Nat.zero_le (4 * r))).2 hnr
  have hexp := Nat.two_mul_sq_add_one_le_two_pow_two_mul r
  have hre : 2 * r ≤ n / 2 + 2 := by dsimp [r]; omega
  have hp : 2 ^ (2 * r) ≤ 2 ^ (n / 2 + 2) := Nat.pow_le_pow_right (by decide) hre
  calc
    n ^ 2 ≤ (4 * r) ^ 2 := hsq
    _ ≤ 8 * 2 ^ (2 * r) := by linarith
    _ ≤ 8 * 2 ^ (n / 2 + 2) := Nat.mul_le_mul_left 8 hp
    _ = 32 * 2 ^ (n / 2) := by rw [pow_add]; ring

/-- The logarithmic exponent in the dense list bound is at most a fixed
multiple of the square-root domain exponent. -/
theorem dense_log_exponent_le_sqrt_exponent (k n c : ℕ)
    (hk : 0 < k) (hn : 2 ≤ n) :
    n + k * (4 * n ^ 2 + 2) + 1 ≤
      (256 * (k + 1) * 2 ^ c) * 2 ^ ((2 * k * n - c) / 2) := by
  let D := 2 * k * n - c
  have hpoly : n + k * (4 * n ^ 2 + 2) + 1 ≤ 8 * (k + 1) * n ^ 2 := by
    have hn_sq : n ≤ n ^ 2 := by nlinarith
    have hone_sq : 1 ≤ n ^ 2 := by linarith
    have htwo_sq : 2 ≤ 2 * n ^ 2 := by linarith
    have hmul := Nat.mul_le_mul_left k htwo_sq
    linarith
  have hsquare := nat_square_le_thirtyTwo_mul_two_pow_half n
  have hhalf : n / 2 ≤ D / 2 + c := by
    have hkn : n ≤ 2 * k * n := by nlinarith
    have hsubadd : 2 * k * n ≤ D + c := by
      dsimp [D]
      rw [Nat.sub_add_eq_max]
      exact le_max_left _ _
    omega
  have hp : 2 ^ (n / 2) ≤ 2 ^ (D / 2 + c) :=
    Nat.pow_le_pow_right (by decide) hhalf
  calc
    n + k * (4 * n ^ 2 + 2) + 1 ≤ 8 * (k + 1) * n ^ 2 := hpoly
    _ ≤ 8 * (k + 1) * (32 * 2 ^ (n / 2)) :=
      Nat.mul_le_mul_left _ hsquare
    _ ≤ 8 * (k + 1) * (32 * 2 ^ (D / 2 + c)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 32 hp)
    _ = (256 * (k + 1) * 2 ^ c) * 2 ^ (D / 2) := by
      rw [pow_add]
      ring


theorem balanced_deviation_le_inverse_fourth_root (D N w I K : ℕ)
    (hN : N = 2 ^ D) (hw : w ≤ N) (hI : 0 < I)
    (hlog : Real.log (2 * I) ≤ (K : ℝ) * 2 ^ (D / 2)) :
    Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I)) / N ≤
      Real.sqrt ((K : ℝ) / 2) / Real.sqrt (Real.sqrt N) := by
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hlog0 : 0 ≤ Real.log (2 * (I : ℝ)) := by
    apply Real.log_nonneg
    have : 1 ≤ 2 * I := by omega
    exact_mod_cast this
  have hR : ((2 ^ (D / 2) : ℕ) : ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by positivity) hNpos.le).2
    rw [hN]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hinside : ((w : ℝ) / 2) * Real.log (2 * I) ≤
      ((K : ℝ) / 2) * (N : ℝ) * Real.sqrt N := by
    have hwR : (w : ℝ) ≤ N := by exact_mod_cast hw
    have h₁ := mul_le_mul hwR hlog hlog0 (by positivity : (0 : ℝ) ≤ N)
    have h₁' := mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h₂ := mul_le_mul_of_nonneg_left hR
      (mul_nonneg (div_nonneg hK0 (by norm_num : (0 : ℝ) ≤ 2)) hNpos.le)
    calc
      ((w : ℝ) / 2) * Real.log (2 * I) =
          (1 / 2) * ((w : ℝ) * Real.log (2 * I)) := by ring
      _ ≤ (1 / 2) * ((N : ℝ) * ((K : ℝ) * 2 ^ (D / 2))) := h₁'
      _ = ((K : ℝ) / 2) * N * (2 ^ (D / 2) : ℕ) := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        ring
      _ ≤ ((K : ℝ) / 2) * N * Real.sqrt N := h₂
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hssN : 0 < Real.sqrt (Real.sqrt N) := Real.sqrt_pos.2 hsN
  have hC : 0 ≤ Real.sqrt ((K : ℝ) / 2) / Real.sqrt (Real.sqrt N) := by positivity
  apply (div_le_iff₀ hNpos).2
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      ((w : ℝ) / 2) * Real.log (2 * I) ≤
          ((K : ℝ) / 2) * N * Real.sqrt N := hinside
      _ = ((Real.sqrt ((K : ℝ) / 2) / Real.sqrt (Real.sqrt N)) * N) ^ 2 := by
        rw [mul_pow, div_pow,
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (K : ℝ) / 2),
          Real.sq_sqrt (Real.sqrt_nonneg N)]
        field_simp [hsN.ne']
        rw [Real.sq_sqrt hNpos.le]


/-- The balanced-padding fluctuation for every subfamily of the actual dense
quadratic list has the required fourth-root decay, with an explicit constant. -/
theorem dense_balanced_deviation_fourth_root
    (k n c w I : ℕ) (hk : 0 < k) (hn : 2 ≤ n) (hI : 0 < I)
    (hw : w ≤ 2 ^ (2 * k * n - c))
    (hIL : I ≤ denseQuadraticListCount (2 ^ k) n (n / 2)) :
    Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I)) /
        (2 ^ (2 * k * n - c) : ℕ) ≤
      Real.sqrt (((256 * (k + 1) * 2 ^ c : ℕ) : ℝ) / 2) /
        Real.sqrt (Real.sqrt (2 ^ (2 * k * n - c) : ℕ)) := by
  let D := 2 * k * n - c
  let U := n + k * (4 * n ^ 2 + 2) + 1
  let K := 256 * (k + 1) * 2 ^ c
  have hpoplog := denseQuadraticListCount_binary_half_log_bound k n hk hn
  have hlogmono : Real.log (2 * I) ≤
      Real.log (2 * denseQuadraticListCount (2 ^ k) n (n / 2)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 hIL
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hlogU : Real.log (2 * I) ≤ (U : ℝ) := by
    calc
      Real.log (2 * I) ≤
          Real.log (2 * denseQuadraticListCount (2 ^ k) n (n / 2)) := hlogmono
      _ ≤ (U : ℕ) * Real.log 2 := by simpa [U] using hpoplog
      _ ≤ U := mul_le_of_le_one_right hU0 hlog2le
  have hUK := dense_log_exponent_le_sqrt_exponent k n c hk hn
  have hUKR : (U : ℝ) ≤ (K : ℝ) * (2 ^ (D / 2) : ℕ) := by
    exact_mod_cast hUK
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hUKR
  apply balanced_deviation_le_inverse_fourth_root D (2 ^ D) w I K rfl hw hI
  exact hlogU.trans hUKR

theorem fourth_root_le_of_le_fourth (N d : ℕ)
    (hN : N ≤ d ^ 4) :
    Real.sqrt (Real.sqrt N) ≤ d := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hNR : (N : ℝ) ≤ (d : ℝ) ^ 4 := by exact_mod_cast hN
  have hsN : Real.sqrt N ≤ (d : ℝ) ^ 2 := by
    apply (Real.sqrt_le_left (sq_nonneg _)).2
    linarith
  apply (Real.sqrt_le_left hd0).2
  exact hsN

theorem dense_rank_error_le_inverse_fourth_root (k n c a : ℕ) :
    (a : ℝ) * ((2 ^ k : ℕ) - 1) / ((2 ^ k : ℕ) ^ (n / 2 + 1)) ≤
      (a : ℝ) * ((2 ^ k : ℕ) - 1) /
        Real.sqrt (Real.sqrt (2 ^ (2 * k * n - c) : ℕ)) := by
  have hpow : 2 ^ (2 * k * n - c) ≤ ((2 ^ k) ^ (n / 2 + 1)) ^ 4 := by
    exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans (by
      have hn : 2 * n ≤ 4 * (n / 2 + 1) := by omega
      have he : 2 * k * n ≤ k * ((n / 2 + 1) * 4) := by
        have := Nat.mul_le_mul_left k hn
        linarith
      calc
        2 ^ (2 * k * n) ≤ 2 ^ (k * ((n / 2 + 1) * 4)) :=
          Nat.pow_le_pow_right (by decide) he
        _ = ((2 ^ k) ^ (n / 2 + 1)) ^ 4 := by rw [pow_mul, pow_mul])
  have hroot := fourth_root_le_of_le_fourth _ _ hpow
  have hdenpos : (0 : ℝ) < ((2 ^ k : ℕ) ^ (n / 2 + 1)) := by positivity
  have hrootpos : (0 : ℝ) < Real.sqrt (Real.sqrt (2 ^ (2 * k * n - c) : ℕ)) := by
    positivity
  apply div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg a) (sub_nonneg.mpr (by
      norm_num
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))))
    hrootpos ?_
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hroot ⊢
  exact hroot


end BinaryFieldCounterexamples
