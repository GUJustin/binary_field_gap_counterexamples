/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.NativeCertificate
/-!
# Main theorem companion: the unpadded native 32-bit decoding list

Section 5.7's paragraph after Corollary 5.18 gives a single word over the
32-bit field with `345166818251997829058040360960` strict-degree codewords
at agreement `63/128`, on every prescribed 27-space and its base-field
translates. This is the explicit pre-padding specialization of Theorem 5.1.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- Section 5.7's pre-padding list: one actual received word over `F_(2^32)`
has the stated exact lower bound on distinct nearby polynomials at `63N/128`. -/
theorem native32_ordinary_list
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (a : B)
    (hB : Fintype.card B=2^32) (hD : (additiveDomain D).card=2^27) :
    ordinaryList (affineDomain (additiveDomain D) a) (2^25) (63*2^20)
      345166818251997829058040360960 := by
  have h := gold_counting_list D a 32 27 6 hB hD (by decide) (by decide) (by decide)
  have hv := Gold.nativeGoldListSize_value
  unfold Gold.nativeGoldListSize at hv
  norm_num only [Nat.reduceMul,Nat.reducePow,Nat.reduceSub,Nat.reduceDiv,Nat.reduceAdd] at h
  norm_num only [Nat.reduceMul,Nat.reducePow,Nat.reduceSub,Nat.reduceDiv,Nat.reduceAdd] at hv
  rw [if_neg (by decide : ¬Even 27)] at h
  norm_num only [Nat.reduceMul,Nat.reducePow,Nat.reduceSub,Nat.reduceAdd] at h
  rw [hv] at h
  convert h using 1 <;> norm_num
end BinaryFieldCounterexamples
