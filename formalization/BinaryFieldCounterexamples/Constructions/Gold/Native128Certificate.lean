/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.NativeCertificate
public import BinaryFieldCounterexamples.Constructions.Gold.ExactRetentionProbability
/-!
# Exact strengthened count for the native 128-bit example

Both simultaneous collision bounds are compared before exact subspace retention.
The collision-subtraction estimate is the larger one for these parameters.
Every numerical identity below uses kernel-checked rational arithmetic.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
/-- The stronger of the two simultaneous exterior-pole counts, with no zero loss. -/
noncomputable def nativeGoldPoleCountSharp : ℕ :=
  max (nativeGoldListSize-(2^15*nativeGoldListSize.choose 2)/(2^128-2^27))
    ⌈(nativeGoldListSize:ℚ)*((2:ℚ)^128-2^27)/
      ((2:ℚ)^128-2^27+2^15*((nativeGoldListSize:ℚ)-1))⌉₊
/-- Exact subspace retention applied to the full strengthened pole count. -/
noncomputable def nativeGoldPaddedCountSharp : ℕ :=
  ⌈paddingRetentionProbability 27 19 12*nativeGoldPoleCountSharp⌉₊
/-- The subtraction estimate exceeds the energy estimate in the native example. -/
theorem nativeGoldPoleCountSharp_value :
    nativeGoldPoleCountSharp=345161081863282574298189647743 := by
  have he : ⌈(nativeGoldListSize:ℚ)*((2:ℚ)^128-2^27)/
      ((2:ℚ)^128-2^27+2^15*((nativeGoldListSize:ℚ)-1))⌉₊ =
        345155345855890900396982497705 := by
    have h := nativeGoldPoleCount_value
    unfold nativeGoldPoleCount at h
    omega
  rw [nativeGoldPoleCountSharp,he,nativeGoldListSize_value]
  norm_num [Nat.choose_two_right]
/-- Exact retained integer count after the sharp pole bound and exact padding. -/
theorem nativeGoldPaddedCountSharp_value :
    nativeGoldPaddedCountSharp=342482627693920113354525730019 := by
  rw [nativeGoldPaddedCountSharp,nativeGoldPoleCountSharp_value,
    paddingRetentionProbability_product 27 19 12 (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]
  rw [Nat.ceil_eq_iff (by decide)]
  norm_num
/-- The improved conservative decimal count and the existing conservative probability both follow. -/
theorem nativeGoldPaddedCountSharp_certificate :
    34248*10^25<nativeGoldPaddedCountSharp ∧
      Real.rpow 2 (-(29889/1000:ℝ))<(nativeGoldPaddedCountSharp:ℝ)/(2:ℝ)^128 := by
  have hcount : 34248*10^25<nativeGoldPaddedCountSharp := by
    rw [nativeGoldPaddedCountSharp_value]
    norm_num
  refine ⟨hcount,nativeGold_probability_lower.trans ?_⟩
  apply div_lt_div_of_pos_right _ (by positivity)
  have hweak : 34247*10^25<nativeGoldPaddedCountSharp := by omega
  exact_mod_cast hweak
end BinaryFieldCounterexamples.Gold
