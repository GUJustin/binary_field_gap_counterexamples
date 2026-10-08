/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.PairAsymptotic
/-!
# Fields for higher-rate lengthening

A list of size at most `2^(d²)` on `2^d` points is separated over an extension
of degree `4*d+4`. The quadratic conversion of Lemma 3.12 still gives a field of
size at most `N^((32/log 2)*log N)` once `d` dominates the fixed codimension.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.HigherRateLengthening

/-- Linear extension degree accommodates all pairwise polynomial collisions
for every selected list of size at most `2^(d²)`. -/
theorem pole_field_capacity (c d J L : ℕ) (hd : 1 ≤ d)
    (hJ : J ≤ 2^d) (hL : L ≤ 2^(d^2)) :
    2^d + J*L^2 < (2^(d+c))^(4*d+4) := by
  have hL2 : L^2 ≤ 2^(2*d^2) := by
    simpa only [←pow_mul, Nat.mul_comm (d^2) 2] using Nat.pow_le_pow_left hL 2
  have hone : 1 ≤ 2^(2*d^2) := Nat.one_le_pow _ _ (by omega)
  calc
    2^d + J*L^2 ≤ 2^d + 2^d*2^(2*d^2) :=
      Nat.add_le_add_left (Nat.mul_le_mul hJ hL2) _
    _ ≤ 2*2^d*2^(2*d^2) := by nlinarith
    _ = 2^(1+d+2*d^2) := by rw [pow_add, pow_add, pow_one]
    _ < 2^((d+c)*(4*d+4)) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      nlinarith
    _ = (2^(d+c))^(4*d+4) := by rw [pow_mul]

/-- The extension and the conversion of Lemma 3.12 have a quadratic binary exponent. -/
theorem final_field_binary_bound (c d : ℕ) (hd : 1 ≤ d) (hc : c ≤ d) :
    (2^(d+c))^(2*(4*d+4)) ≤ 2^(32*d^2) := by
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have hmul := Nat.mul_le_mul_right (2*(4*d+4)) (show d+c≤2*d by omega)
  nlinarith

/-- The quadratic binary exponent is the claimed quasipolynomial field bound. -/
theorem final_field_real_bound (d q : ℕ) (hq : q ≤ 2^(32*d^2)) :
    (q : ℝ) ≤ ((2^d : ℕ) : ℝ)^((32 / Real.log 2) * Real.log (2^d : ℕ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (q : ℝ) ≤ ((2^(32*d^2) : ℕ) : ℝ) := by exact_mod_cast hq
    _ = Real.exp ((32*d^2 : ℕ)*Real.log 2) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [←Real.log_pow, Real.exp_log]
      positivity
    _ = ((2^d : ℕ) : ℝ)^((32 / Real.log 2) * Real.log (2^d : ℕ)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      congr 1
      push_cast
      field_simp

end BinaryFieldCounterexamples.HigherRateLengthening
