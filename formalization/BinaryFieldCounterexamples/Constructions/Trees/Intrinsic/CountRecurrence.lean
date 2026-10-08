/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.FrameArithmetic
/-!
# The minimal intrinsic-tree count recurrence

The exact product count already used by the template development satisfies
the recurrence for `C_h` in Lemma 6.6, Section 6.2 of the paper. These arithmetic
identities let the intrinsic counting API expose both paper formulas without
recounting representations.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open scoped BigOperators

/-- Splitting an ordered square binary frame after `a` columns. -/
theorem binaryFrameProduct_add_diagonal (a b : ℕ) :
    binaryFrameProduct (a+b) (a+b)=
      binaryFrameProduct (a+b) a*2^(a*b)*binaryFrameProduct b b := by
  unfold binaryFrameProduct
  rw [Finset.prod_range_add]
  have he (i : ℕ) : 2^(a+b)-2^(a+i)=2^a*(2^b-2^i) := by
    rw [pow_add,pow_add,Nat.mul_sub_left_distrib]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_range,←pow_mul]
  ring

/-- Adding the first column to a square binary frame separates the first test. -/
theorem binaryFrameProduct_succ_diagonal (d : ℕ) :
    binaryFrameProduct (d+1) (d+1)=(2^(d+1)-1)*2^d*binaryFrameProduct d d := by
  have h := binaryFrameProduct_add_diagonal 1 d
  rw [show 1+d=d+1 by omega] at h
  simpa [show binaryFrameProduct (d+1) 1=2^(d+1)-1 by simp [binaryFrameProduct]] using h

/-- The minimal-domain count `C_h` appearing in Lemma 6.6. -/
def intrinsicTreeMinimalCount (h : ℕ) : ℕ := treeSupportCount h (2^h-1)

/-- The initial value in the paper's count recurrence is 56. -/
theorem intrinsicTreeMinimalCount_two : intrinsicTreeMinimalCount 2=56 := by
  norm_num [intrinsicTreeMinimalCount,treeSupportCount,treeDenominator,Finset.prod_range_succ]

/-- Lemma 6.6's recurrence, at actual height `n+3`, with child dimension
`r=2^(n+2)-1`. -/
theorem intrinsicTreeMinimalCount_succ (n : ℕ) :
    let r := 2^(n+2)-1
    intrinsicTreeMinimalCount (n+3)=
      (2^(2^(n+3)-1)-1)*gaussianBinomial 2 (2*r) r*2^(r^2)*
        intrinsicTreeMinimalCount (n+2)^2 := by
  dsimp only
  let r := 2^(n+2)-1
  have ht : 2^(n+3)-1=2*r+1 := by
    have hp : 1≤(2:ℕ)^(n+2) := Nat.one_le_pow _ _ (by decide)
    dsimp [r]
    rw [show n+3=n+2+1 by omega,pow_succ]
    omega
  have hc := treeSupportCount_mul_denominator n (2^(n+2)-1) le_rfl
  have hn := treeSupportCount_mul_denominator (n+1) (2^(n+3)-1) (by simp)
  have hd : treeDenominator (n+3)=2^(2*r)*treeDenominator (n+2)^2 := by
    rfl
  change intrinsicTreeMinimalCount (n+2)*treeDenominator (n+2)=binaryFrameProduct r r at hc
  have hn' : intrinsicTreeMinimalCount (n+3)*treeDenominator (n+3)=
      binaryFrameProduct (2*r+1) (2*r+1) := by
    simpa [intrinsicTreeMinimalCount,show n+1+2=n+3 by omega,ht] using hn
  have hs := binaryFrameProduct_add_diagonal r r
  rw [show r+r=2*r by omega] at hs
  rw [binaryFrameProduct_succ_diagonal,hs,
    binaryFrameProduct_eq_gaussian_mul (2*r) r (by omega)] at hn'
  rw [←hc,hd] at hn'
  have he : intrinsicTreeMinimalCount (n+3)*(2^(2*r)*treeDenominator (n+2)^2)=
      ((2^(2*r+1)-1)*gaussianBinomial 2 (2*r) r*2^(r^2)*
        intrinsicTreeMinimalCount (n+2)^2)*(2^(2*r)*treeDenominator (n+2)^2) := by
    calc
      _=_ := hn'
      _=_ := by ring
  have hpos : 0<2^(2*r)*treeDenominator (n+2)^2 := by
    have := treeDenominator_pos (n+2)
    positivity
  rw [ht]
  exact Nat.eq_of_mul_eq_mul_right hpos he

end BinaryFieldCounterexamples.Trees
