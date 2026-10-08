/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianLowerBound
import Mathlib.Tactic.NormNum
/-!
# Finite power bound for the dense Gold regime
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- The explicit binary exponent retained by the three factors in the Gold
locator population. -/
def denseGoldExponent (c d t : ℕ) : ℕ :=
  2*t+(d+c-t*(c+if Even d then 1 else 0)-1)+2*(t*(d/2-t))

/-- Extension degree obtained by rounding the retained Gold exponent down to a
multiple of the base-field dimension. -/
def denseGoldExtensionDegree (c d t : ℕ) : ℕ :=
  denseGoldExponent c d t/(d+c)

/-- The literal Gold locator count is at least the corresponding binary power. -/
theorem denseGold_power_le_list (c d t : ℕ) (htd : t≤d/2)
    (hΔ : 1≤d+c-t*(c+if Even d then 1 else 0)) :
    2^(denseGoldExponent c d t) ≤
      2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
        gaussianBinomial 4 (d/2) t := by
  let Δ := d+c-t*(c+if Even d then 1 else 0)
  have hsub : 2^(Δ-1)≤2^Δ-1 := by
    have hlt : 2^(Δ-1)<2^Δ := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hG := pow_mul_sub_le_gaussianBinomial 4 (d/2) t (by decide) htd
  have hfour : 4^(t*(d/2-t))=2^(2*(t*(d/2-t))) := by
    rw [show 4=2^2 by norm_num,←pow_mul]
  rw [hfour] at hG
  dsimp [denseGoldExponent,Δ] at *
  rw [pow_add,pow_add]
  exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hsub) hG

/-- The rounded-down extension field fits inside the literal Gold list size. -/
theorem denseGold_extension_card_le_list (c d t : ℕ) (htd : t≤d/2)
    (hΔ : 1≤d+c-t*(c+if Even d then 1 else 0)) :
    (2^(d+c))^(denseGoldExtensionDegree c d t) ≤
      2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
        gaussianBinomial 4 (d/2) t := by
  apply le_trans ?_ (denseGold_power_le_list c d t htd hΔ)
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_div_le (denseGoldExponent c d t) (d+c)

/-- Rounding the retained exponent to a base-field multiple loses fewer than
`d+c` binary exponent units. -/
theorem denseGold_rounding_lower (c d t : ℕ) (hm : 0<d+c)
    (hell : d+c≤denseGoldExponent c d t) :
    denseGoldExponent c d t-(d+c) <
      (d+c)*denseGoldExtensionDegree c d t := by
  have h := Nat.lt_mul_div_succ (denseGoldExponent c d t) hm
  dsimp [denseGoldExtensionDegree]
  rw [Nat.mul_add] at h
  omega

end BinaryFieldCounterexamples.Gold
