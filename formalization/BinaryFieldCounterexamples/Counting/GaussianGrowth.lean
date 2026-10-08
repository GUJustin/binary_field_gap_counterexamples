/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianLowerBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Elementary growth bounds for Gaussian coefficients

This file records integral upper and lower bounds for Gaussian coefficients and
for the dense quadratic-form population used later in the paper.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- A crude uniform upper bound for the integral Gaussian coefficient. -/
theorem gaussianPascal_le_two_pow_mul_pow (q n k : ℕ) (hq : 1 ≤ q) (hk : k ≤ n) :
    gaussianPascal q n k ≤ 2 ^ n * q ^ (k * (n - k)) := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp [gaussianPascal]
  | succ n ih =>
      cases k with
      | zero =>
          rw [gaussianPascal_zero]
          simp only [zero_mul, pow_zero, mul_one]
          exact one_le_pow₀ (by decide : 1 ≤ 2)
      | succ k =>
          by_cases hkn : k = n
          · subst k
            rw [gaussianPascal_self]
            simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
            exact one_le_pow₀ (by decide : 1 ≤ 2)
          · have hklt : k < n := by omega
            rw [gaussianPascal_succ]
            have hleft := ih k (by omega)
            have hright := ih (k + 1) (by omega)
            have hqmono (a b : ℕ) (hab : a ≤ b) : q ^ a ≤ q ^ b :=
              Nat.pow_le_pow_right (by omega) hab
            have hsub : n + 1 - (k + 1) = n - k := by omega
            have hsub' : n - k = (n - (k + 1)) + 1 := by omega
            have he₁ : k * (n - k) ≤ (k + 1) * (n + 1 - (k + 1)) := by
              rw [hsub]
              exact Nat.mul_le_mul_right _ (Nat.le_succ k)
            have he₂ : (k + 1) + (k + 1) * (n - (k + 1)) =
                (k + 1) * (n + 1 - (k + 1)) := by
              rw [hsub, hsub', Nat.mul_add]
              ring
            calc
              gaussianPascal q n k + q ^ (k + 1) * gaussianPascal q n (k + 1) ≤
                  2 ^ n * q ^ (k * (n-k)) +
                    q^(k+1) * (2^n*q^((k+1)*(n-(k+1)))) :=
                Nat.add_le_add hleft (Nat.mul_le_mul_left _ hright)
              _ ≤ 2^n * q^((k+1)*(n+1-(k+1))) +
                    2^n * q^((k+1)*(n+1-(k+1))) := by
                apply Nat.add_le_add
                · exact Nat.mul_le_mul_left _ (hqmono _ _ he₁)
                · calc
                    q^(k+1) * (2^n*q^((k+1)*(n-(k+1)))) =
                        2^n * (q^(k+1)*q^((k+1)*(n-(k+1)))) := by ring
                    _ = _ := by
                      rw [← pow_add, he₂]
                    _ ≤ _ := le_rfl
              _ = 2^(n+1)*q^((k+1)*(n+1-(k+1))) := by
                rw [pow_succ]
                ring

/-- The natural version of the dense quadratic-form population. -/
def denseQuadraticListCount (q n t : ℕ) : ℕ :=
  q ^ (2 * t) * ((q ^ t - 1) / (q - 1)) * gaussianPascal (q ^ 2) n t

/-- The geometric scalar factor in the dense population lies between one and
`q^t`. -/
theorem geometricQuotient_bounds (q t : ℕ) (hq : 1 < q) (ht : 0 < t) :
    1 ≤ (q ^ t - 1) / (q - 1) ∧ (q ^ t - 1) / (q - 1) ≤ q ^ t := by
  have hden : 0 < q - 1 := by omega
  have hpow : q ≤ q^t := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ t)
  constructor
  · apply (Nat.le_div_iff_mul_le hden).2
    simpa only [one_mul] using Nat.sub_le_sub_right hpow 1
  · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

/-- Two-sided power bounds for the actual natural dense population. -/
theorem denseQuadraticListCount_bounds (q n t : ℕ)
    (hq : 1 < q) (ht : 0 < t) (htn : t ≤ n) :
    q ^ (2 * t + 2 * t * (n - t)) ≤ denseQuadraticListCount q n t ∧
      denseQuadraticListCount q n t ≤
        2 ^ n * q ^ (3 * t + 2 * t * (n - t)) := by
  have hg := geometricQuotient_bounds q t hq ht
  have hbase : 1 ≤ q^2 := one_le_pow₀ (by omega)
  have hgl := pow_mul_sub_le_gaussianPascal (q^2) n t htn
  have hgu := gaussianPascal_le_two_pow_mul_pow (q^2) n t hbase htn
  constructor
  · dsimp [denseQuadraticListCount]
    calc
      q ^ (2*t+2*t*(n-t)) = q^(2*t) * (q^2)^(t*(n-t)) := by
        have hp : (q^2)^(t*(n-t)) = q^(2*(t*(n-t))) :=
          (pow_mul q 2 (t*(n-t))).symm
        rw [hp, ← pow_add]
        congr 1
        ring
      _ ≤ q^(2*t) * ((q^t-1)/(q-1)) * gaussianPascal (q^2) n t := by
        simpa only [one_mul, mul_assoc] using
          Nat.mul_le_mul_left (q^(2*t)) (Nat.mul_le_mul hg.1 hgl)
  · dsimp [denseQuadraticListCount]
    calc
      q^(2*t)*((q^t-1)/(q-1))*gaussianPascal (q^2) n t ≤
          q^(2*t)*q^t*(2^n*(q^2)^(t*(n-t))) := by
        simpa only [mul_assoc] using
          Nat.mul_le_mul_left (q^(2*t)) (Nat.mul_le_mul hg.2 hgu)
      _ = 2^n*q^(3*t+2*t*(n-t)) := by
        calc
          q^(2*t)*q^t*(2^n*(q^2)^(t*(n-t))) =
              2^n*(q^(2*t)*q^t*(q^2)^(t*(n-t))) := by ring
          _ = 2^n*q^(3*t+2*t*(n-t)) := by
            have hp : (q^2)^(t*(n-t)) = q^(2*(t*(n-t))) :=
              (pow_mul q 2 (t*(n-t))).symm
            rw [hp, ← pow_add, ← pow_add]
            congr 1
            ring

/-- At the middle rank, the lower exponent already has quadratic size. -/
theorem halfRank_lower_exponent (n : ℕ) :
    2 * (n / 2) ^ 2 ≤
      2 * (n / 2) + 2 * (n / 2) * (n - n / 2) := by
  have hhalf : n / 2 ≤ n - n / 2 := by omega
  have hmul := Nat.mul_le_mul_left (n / 2) hhalf
  calc
    2 * (n / 2) ^ 2 = 2 * ((n / 2) * (n / 2)) := by ring
    _ ≤ 2 * ((n / 2) * (n - n / 2)) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (n / 2) * (n - n / 2) := by ring
    _ ≤ 2 * (n / 2) + 2 * (n / 2) * (n - n / 2) :=
      Nat.le_add_left _ _

/-- A deliberately coarse quadratic upper bound for the middle-rank exponent. -/
theorem halfRank_upper_exponent (n : ℕ) :
      3 * (n / 2) + 2 * (n / 2) * (n - n / 2) ≤ 4 * n ^ 2 + 2 := by
  have hhalf : n / 2 ≤ n := Nat.div_le_self n 2
  have hdiff : n - n / 2 ≤ n := Nat.sub_le n _
  have hmul : (n / 2) * (n - n / 2) ≤ n * n :=
    Nat.mul_le_mul hhalf hdiff
  nlinarith

/-- Binary-power form of the dense population estimates at middle rank. -/
theorem denseQuadraticListCount_binary_half_bounds (k n : ℕ)
    (hk : 0 < k) (hn : 2 ≤ n) :
    2 ^ (2 * k * (n / 2) ^ 2) ≤
        denseQuadraticListCount (2 ^ k) n (n / 2) ∧
      denseQuadraticListCount (2 ^ k) n (n / 2) ≤
        2 ^ (n + k * (4 * n ^ 2 + 2)) := by
  have hq : 1 < 2^k := by
    exact one_lt_pow₀ (by decide) hk.ne'
  have ht : 0 < n / 2 := by omega
  have htn : n / 2 ≤ n := Nat.div_le_self n 2
  obtain ⟨hL, hU⟩ := denseQuadraticListCount_bounds (2^k) n (n/2) hq ht htn
  constructor
  · apply le_trans ?_ hL
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have h := halfRank_lower_exponent n
    nlinarith
  · apply le_trans hU
        ?_
    rw [← pow_mul, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have h := halfRank_upper_exponent n
    nlinarith

end BinaryFieldCounterexamples
