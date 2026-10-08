/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.PowerGrowth
public import BinaryFieldCounterexamples.Counting.TreePositivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-!
# Growth of the exact decision-tree support recursion

The literal natural-number quotient and recursion satisfy positive uniform
power bounds. Height induction adds the Gaussian exponent to the preceding
avoidance exponent, while all fixed multipliers are proved positive.
-/
@[expose] public section

namespace BinaryFieldCounterexamples
/-- The initial avoidance count has positive linear growth in domain size. -/
theorem avoidingTreeSupportCount_two_growth :
    HasBinaryPowerGrowth (avoidingTreeSupportCount 2) 1 := by
  refine ⟨28/8,168/8,by norm_num,by norm_num,3,?_⟩
  intro d hd
  have hx : 1≤2^(d-3) := Nat.one_le_pow _ _ (by decide)
  have hp : 2^d=8*2^(d-3) := by
    calc
      2^d=2^((d-3)+3) := by congr 1; omega
      _=_ := by rw [pow_add]; ring
  have hl : 28*2^(d-3) ≤ 28*(6*2^(d-3)-5) := by omega
  have hu : 28*(6*2^(d-3)-5) ≤ 168*2^(d-3) := by omega
  have hpR : (2:ℝ)^d=8*(2:ℝ)^(d-3) := by exact_mod_cast hp
  have hlR : 28*(2:ℝ)^(d-3) ≤ ((28*(6*2^(d-3)-5):ℕ):ℝ) := by exact_mod_cast hl
  have huR : ((28*(6*2^(d-3)-5):ℕ):ℝ) ≤ 168*(2:ℝ)^(d-3) := by exact_mod_cast hu
  simp only [avoidingTreeSupportCount,pow_one]
  constructor <;> linarith

/-- The exact recursive support count has the claimed exponent at every
fixed height; all constants are independent of the growing dimension. -/
theorem avoidingTreeSupportCount_growth (h : ℕ) (hh : 2≤h) :
    HasBinaryPowerGrowth (avoidingTreeSupportCount h) (2^h-h-1) := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    obtain _|_|_|n := h
    · omega
    · omega
    · simpa using avoidingTreeSupportCount_two_growth
    let r := 2^(n+2)-1
    let A := (2^(n+4)-1)*2^(r^2)*treeSupportCount (n+2) r
    have hA : 0<A := by
      have hp : 1<2^(n+4) := by
        have := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤n+4 by omega)
        omega
      have ht : 0<treeSupportCount (n+2) r := treeSupportCount_at_min_pos (n+2) (by omega)
      dsimp [A]
      exact mul_pos (mul_pos (Nat.sub_pos_of_lt hp) (pow_pos (by decide) _)) ht
    have hf := (ih (n+2) (by omega) (by omega)).shift 1
    have hg := (gaussianBinomial_two_growth r).shift (1+r)
    have hprod := (hf.mul hg).const_mul A hA
    have hexp : (2^(n+2)-(n+2)-1)+r=2^(n+3)-(n+3)-1 := by
      have := (n+2).lt_two_pow_self
      have hp : 2^(n+3)=2*2^(n+2) := by
        calc
          2^(n+3)=2^((n+2)+1) := by congr 1
          _=2*2^(n+2) := by rw [pow_succ]; omega
      dsimp [r]
      omega
    rw [hexp] at hprod
    apply hprod.congr
    intro d
    rw [← Nat.sub_sub]
    simp only [avoidingTreeSupportCount]
    dsimp [A,r]
    ring
end BinaryFieldCounterexamples
