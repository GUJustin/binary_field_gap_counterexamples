/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.DimensionArithmetic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Field.Subfield.Basic
/-!
# Arithmetic remarks in Sections 5.1 and 5.5

These are the density obstruction preceding Corollary 5.2 and the strict
Johnson comparison following Corollary 5.15. Implementation facts and field
representation claims are not hypotheses of the arithmetic results.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Section 5.1: if `m ≥ 2d` and `t ≥ 2`, the Gold density parameter is
strictly below one, with either parity correction. -/
theorem delta_lt_one_of_double_dimension (m d t : ℕ)
    (hm : 2*d ≤ m) (ht : 2 ≤ t) :
    m-t*(m-d+if Even d then 1 else 0) < 1 := by
  have hd : d ≤ m := by omega
  have hmul : 2*(m-d+if Even d then 1 else 0) ≤
      t*(m-d+if Even d then 1 else 0) := Nat.mul_le_mul_right _ ht
  split_ifs at hmul ⊢ <;> omega

/-- Section 5.1's density obstruction in the paper's signed convention:
`Delta = m-t(m-d+iota)` is strictly below one whenever `m ≥ 2d` and `t ≥ 2`.
This version does not truncate the possibly negative density parameter. -/
theorem delta_signed_lt_one_of_double_dimension (m d t : ℕ)
    (hm : 2*d ≤ m) (ht : 2 ≤ t) :
    (m : ℤ)-(t : ℤ)*((m : ℤ)-(d : ℤ)+if Even d then 1 else 0) < 1 := by
  have hd : d ≤ m := by omega
  have hnat : m ≤ t*(m-d+if Even d then 1 else 0) := by
    have h := delta_lt_one_of_double_dimension m d t hm ht
    omega
  have hc : (m : ℤ) ≤ (t : ℤ)*((m-d+if Even d then 1 else 0 : ℕ) : ℤ) := by
    exact_mod_cast hnat
  have hcorr : ((m-d+if Even d then 1 else 0 : ℕ) : ℤ) =
      (m : ℤ)-(d : ℤ)+if Even d then 1 else 0 := by
    split_ifs <;> simp [Int.ofNat_sub hd]
  rw [hcorr] at hc
  linarith

/-- Section 5.1, the LeanVM arithmetic example: the signed expression
`64 - 43t` is below one for every `t ≥ 2`. -/
theorem leanVM_delta_lt_one (t : ℕ) (ht : 2 ≤ t) :
    (64 : ℤ)-43*(t : ℤ) < 1 := by omega

/-- Section 5.1, the Flock arithmetic example: dimension at most 24 in a
128-dimensional binary field cannot satisfy the positive-density hypothesis. -/
theorem flock_delta_lt_one (d t : ℕ) (hd : d ≤ 24) (ht : 2 ≤ t) :
    128-t*(128-d+if Even d then 1 else 0) < 1 := by
  exact delta_lt_one_of_double_dimension 128 d t (by omega) ht

/-- The prose following Corollary 5.15: the limiting half-rate agreement
`5/8` lies strictly below the Johnson fraction `1/√2`. -/
theorem half_rate_limit_lt_johnson : (5 : ℝ)/8 < 1/Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (lt_div_iff₀ hp).mpr
  nlinarith [Real.sqrt_nonneg 2]

/-- Section 5.1's smallest-containing-field observation: a binary domain
containing a field generator generates the entire ambient field. Thus a span
containing `1,u` cannot be contained in a proper subfield when `u` generates
the ambient field, as in the stated LeanVM/Flock domain examples. -/
theorem containing_generator_closure_eq_top {B : Type*} [Field B]
    (D : AddSubgroup B) (u : B) (hu : u ∈ D)
    (hgen : Subfield.closure ({u} : Set B) = ⊤) :
    Subfield.closure (D : Set B) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subfield.closure_mono
  intro x hx
  simpa only [Set.mem_singleton_iff] using hx ▸ hu

/-- Section 5.1's smallest-containing-field observation in its universal form:
every subfield containing a domain that contains a field generator is the
whole ambient field. The generator condition is explicit, independent of a
particular field representation used by an implementation. -/
theorem containing_generator_subfield_eq_top {B : Type*} [Field B]
    (D : AddSubgroup B) (u : B) (hu : u ∈ D)
    (hgen : Subfield.closure ({u} : Set B) = ⊤)
    (K : Subfield B) (hD : (D : Set B) ⊆ K) : K = ⊤ := by
  apply top_unique
  rw [← containing_generator_closure_eq_top D u hu hgen]
  exact Subfield.closure_le.mpr hD

end BinaryFieldCounterexamples.Gold
