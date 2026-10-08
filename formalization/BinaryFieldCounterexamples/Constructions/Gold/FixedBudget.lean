/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianLowerBound
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# A fixed-parameter Gold collision budget bound
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- The displayed exponent comparison is sufficient for the degree-`e`
extension field to fit below the Gold collision budget `δ L`. -/
theorem fixed_gold_field_le_collision_budget (d e t : ℕ)
    (hdt : 2*t≤d)
    (hexp : e*(d+1)≤d+(d-2*t)+2*(t*(d/2-t))) :
    (2^(d+1))^e ≤
      (2^d/2^(2*t)) *
        (2^(2*t)*(2^(d+1-2*t)-1)*gaussianBinomial 4 (d/2) t) := by
  have ht : t≤d/2 := by omega
  have hδ : 2^d/2^(2*t)=2^(d-2*t) := Nat.pow_div hdt (by decide)
  have hΔ : d+1-2*t=(d-2*t)+1 := by omega
  have hsub : 2^(d-2*t)≤2^(d+1-2*t)-1 := by
    rw [hΔ,pow_succ]
    omega
  have hG : 4^(t*(d/2-t))≤gaussianBinomial 4 (d/2) t :=
    pow_mul_sub_le_gaussianBinomial 4 (d/2) t (by decide) ht
  have hprod : 2^(d-2*t)*2^(2*t)*2^(d-2*t)*4^(t*(d/2-t)) ≤
      (2^d/2^(2*t)) *
        (2^(2*t)*(2^(d+1-2*t)-1)*gaussianBinomial 4 (d/2) t) := by
    rw [hδ]
    calc
      _ = (2^(d-2*t)*2^(2*t))*(2^(d-2*t)*4^(t*(d/2-t))) := by ring
      _ ≤ (2^(d-2*t)*2^(2*t))*
          ((2^(d+1-2*t)-1)*gaussianBinomial 4 (d/2) t) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hsub hG)
      _ = _ := by ring
  apply le_trans ?_ hprod
  rw [←pow_mul]
  have hfour (n : ℕ) : 4^n=2^(2*n) := by
    rw [show 4=2^2 by norm_num,←pow_mul]
  rw [hfour,←pow_add,←pow_add,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  calc
    (d+1)*e = e*(d+1) := by ring
    _ ≤ d+(d-2*t)+2*(t*(d/2-t)) := hexp
    _ = d-2*t+2*t+(d-2*t)+2*(t*(d/2-t)) := by
      rw [Nat.sub_add_cancel hdt]

end BinaryFieldCounterexamples.Gold
