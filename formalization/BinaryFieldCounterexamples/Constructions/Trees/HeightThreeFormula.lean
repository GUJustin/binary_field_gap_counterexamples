/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
public import Mathlib.Tactic
/-!
# The closed height-three avoiding count

Section 6.3 gives the closed product for `M₃(d)` with `w=2^(d-4)`.
The identity below derives it from the proved recursive count. The leading
coefficient is exactly `105/16`, without decimal approximation.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- Section 6.3's height-three product: `M₃(d)=71680(6w-5)(w-1)(w-2)(w-4)`. -/
theorem avoidingTreeSupportCount_three_closed (d : ℕ) (hd : 7 ≤ d) :
    let w := 2^(d-4)
    avoidingTreeSupportCount 3 d = 71680*(6*w-5)*(w-1)*(w-2)*(w-4) := by
  dsimp only
  have hsub : d-1-3=d-4 := by omega
  have hp : 4 ≤ 2^(d-4) := by
    calc
      4 = 2^2 := by norm_num
      _ ≤ 2^(d-4) := Nat.pow_le_pow_right (by decide) (by omega)
  have hg := gaussianPascal_frame_product 2 (d-4) 3 (by decide) (by omega)
  rw [←gaussianBinomial_eq_gaussianPascal 2 (d-4) 3 (by decide)] at hg
  norm_num [Finset.prod_range_succ] at hg
  have hgn : gaussianBinomial 2 (d-4) 3 * 168 =
      (2^(d-4)-1)*(2^(d-4)-2)*(2^(d-4)-4) := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ 2^(d-4)),
      Nat.cast_sub (by omega : 2 ≤ 2^(d-4)), Nat.cast_sub hp]
    push_cast
    exact hg
  have hbase : treeSupportCount 2 3=56 := by
    norm_num [treeSupportCount,treeDenominator,Finset.prod_range_succ]
  simp only [avoidingTreeSupportCount,show (0+2 : ℕ)=2 by omega,
    show (0+4 : ℕ)=4 by omega, hsub,hbase]
  norm_num only [pow_succ, pow_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
    Nat.reducePow]
  rw [hsub,hbase]
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 168)
  calc
    _ = 71680*168*(6*2^(d-4)-5)*(gaussianBinomial 2 (d-4) 3*168) := by ring
    _ = _ := by rw [hgn]; ring

/-- Section 6.3's asymptotic coefficient is exactly `105/16`: the coefficient
of `w⁴` in the closed product, rescaled by `N=16w`, equals that rational. -/
theorem avoidingTreeSupportCount_three_leading_coefficient :
    (71680 : ℚ)*6/16^4 = 105/16 := by norm_num
end BinaryFieldCounterexamples
