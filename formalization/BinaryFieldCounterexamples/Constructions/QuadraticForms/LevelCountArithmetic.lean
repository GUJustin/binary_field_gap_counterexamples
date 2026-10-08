/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.DegenerateZeroCount

/-!
# Arithmetic separating affine quadratic level counts

The level-set necessity remark after Corollary 5.23 uses that, when `b > 2`,
a power of `b` cannot equal `b - 1` times another power of `b`.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticGeometry

/-- The level-set necessity remark after Corollary 5.23: for `b > 2`, the
coefficient `b - 1` cannot be absorbed by changing a power of `b`. -/
theorem power_ne_pred_mul_power (b i j : ℕ) (hb : 2 < b) :
    b ^ i ≠ (b - 1) * b ^ j := by
  have hj : 0 < b ^ j := pow_pos (by omega) _
  have hpred : b - 1 + 1 = b := by omega
  intro he
  by_cases hij : i ≤ j
  · have hp := Nat.pow_le_pow_right (show 0 < b by omega) hij
    have hpredgt : 1 < b - 1 := by omega
    nlinarith
  · have hp := Nat.pow_le_pow_right (show 0 < b by omega)
      (show j + 1 ≤ i by omega)
    rw [pow_succ] at hp
    nlinarith

/-- The level-set necessity remark after Corollary 5.23: the elliptic
threshold has a positive deficit, with exact natural-number subtraction and
the baseline identity used when homogenizing an affine quadratic function. -/
theorem elliptic_threshold_decomposition (b d t : ℕ) (hb : 2 < b)
    (ht : 0 < t) (htd : 2*t ≤ d) :
    let C := (b-1)*b^(d-t-1)
    let T := b^(d-1)-C
    0 < C ∧ T+C=b^(d-1) ∧ T<b^(d-1) ∧
      b^(d-1)+(b-1)*b^(d-1)=b^d := by
  have hbpos : 0 < b := by omega
  have hpos : 0 < (b-1)*b^(d-t-1) := Nat.mul_pos (by omega) (pow_pos hbpos _)
  have hpowt : b ≤ b^t := by
    have h := Nat.pow_le_pow_right hbpos (show 1 ≤ t by omega)
    simpa only [pow_one] using h
  have hle : (b-1)*b^(d-t-1) ≤ b^(d-1) := by
    calc
      (b-1)*b^(d-t-1) ≤ b^t*b^(d-t-1) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = b^(d-1) := by rw [← pow_add]; congr 1; omega
  have hpred : b-1+1=b := by omega
  have hpow : b^d=b^(d-1)*b := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨hpos, Nat.sub_add_cancel hle, Nat.sub_lt (by positivity) hpos, ?_⟩
  rw [hpow]
  nlinarith

end BinaryFieldCounterexamples.QuadraticGeometry
