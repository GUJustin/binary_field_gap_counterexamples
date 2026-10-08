/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Rat.Floor

/-!
# Collision averaging

This file proves the finite counting lemma used to turn a family of indexed
challenges into many distinct challenge values.  Collisions are unordered: a fiber of
size `v` contributes `v.choose 2`.

The main theorem is Lemma 3.19 (Collision averaging), p. 27, of the paper.  It
chooses one parameter at which both the additive and second-moment image bounds
hold.  The final corollary records the loss of at most one value when zero is
discarded.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Finset

variable {Index Parameter Label : Type*} [DecidableEq Label]

/-- The number of unordered pairs of indices in `S` on which `label` agrees.

Writing the count as a sum of `v.choose 2` over the nonempty fibers avoids any
choice of an ordering on the index type. -/
def unorderedCollisionCount (S : Finset Index) (label : Index → Label) : ℕ :=
  ∑ z ∈ S.image label, (S.filter fun i ↦ label i = z).card.choose 2

/-- Natural-number ceiling division, totalized to zero when the numerator is
zero.  The collision theorem only uses it when the denominator is positive or
the numerator is zero. -/
def natCeilDiv (a b : ℕ) : ℕ :=
  if a = 0 then 0 else (a - 1) / b + 1

/-- A multiplicative upper bound on a numerator bounds its ceiling quotient. -/
theorem natCeilDiv_le_of_le_mul {a b c : ℕ} (hb : 0 < b)
    (h : a ≤ c * b) : natCeilDiv a b ≤ c := by
  by_cases ha : a = 0
  · subst a
    simp [natCeilDiv]
  have hc : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    simp only [zero_mul] at h
    exact ha (Nat.eq_zero_of_le_zero h)
  rw [natCeilDiv, ite_eq_right ha]
  apply Nat.succ_le_iff.mpr
  rw [Nat.div_lt_iff_lt_mul hb]
  omega

/-- For a positive denominator, the natural ceiling quotient has the usual
order characterization, including a zero numerator. -/
theorem natCeilDiv_le_iff_le_mul {a b c : ℕ} (hb : 0 < b) :
    natCeilDiv a b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h
    by_cases ha : a = 0
    · simp [ha]
    rw [natCeilDiv, ite_eq_right ha, Nat.succ_le_iff, Nat.div_lt_iff_lt_mul hb] at h
    omega
  · exact natCeilDiv_le_of_le_mul hb

/-- The integer formula used by collision averaging is exactly the natural
ceiling of the rational quotient appearing in the paper's companion theorem.
The positive denominator hypothesis is essential for the chosen totalization;
the numerator may be zero. -/
theorem natCeilDiv_eq_rat_ceil (a b : ℕ) (hb : 0 < b) :
    natCeilDiv a b = ⌈(a : ℚ) / b⌉₊ := by
  apply eq_of_forall_ge_iff
  intro c
  rw [natCeilDiv_le_iff_le_mul hb, Nat.ceil_le,
    div_le_iff₀ (Nat.cast_pos.mpr hb), ← Nat.cast_mul, Nat.cast_le]

/-- The square of a fiber size counts its diagonal plus twice its unordered pairs. -/
theorem sq_eq_add_two_mul_choose_two (n : ℕ) :
    n ^ 2 = n + 2 * n.choose 2 := by
  rw [Nat.choose_two_right]
  rw [mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  cases n with
  | zero => simp
  | succ n =>
      simp only [pow_two, Nat.succ_sub_one]
      rw [Nat.mul_succ]
      omega

/-- A nonempty fiber's excess beyond its first element is at most its
number of unordered pairs. -/
theorem pred_le_choose_two {n : ℕ} (hn : 0 < n) :
    n - 1 ≤ n.choose 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp
  rw [Nat.choose_two_right]
  rw [Nat.le_div_iff_mul_le Nat.two_pos]
  have htwo : 2 ≤ n := by omega
  calc
    (n - 1) * 2 ≤ (n - 1) * n := Nat.mul_le_mul_left _ htwo
    _ = n * (n - 1) := Nat.mul_comm _ _

/-- The nonempty fibers over a finite image partition the source finset. -/
theorem sum_fiber_card_eq (S : Finset Index) (label : Index → Label) :
    ∑ z ∈ S.image label, (S.filter fun i ↦ label i = z).card = S.card := by
  simpa using (Finset.card_eq_sum_card_image label S).symm

/-- The additive image bound at a fixed parameter: every repeated index beyond
the first in a fiber can be charged to a different unordered colliding pair. -/
theorem card_sub_image_card_le_unorderedCollisionCount
    (S : Finset Index) (label : Index → Label) :
    S.card - (S.image label).card ≤ unorderedCollisionCount S label := by
  classical
  have hfiber_pos : ∀ z ∈ S.image label,
      0 < (S.filter fun i ↦ label i = z).card := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  have hsum :
      ∑ z ∈ S.image label, ((S.filter fun i ↦ label i = z).card - 1) ≤
        unorderedCollisionCount S label := by
    apply Finset.sum_le_sum
    intro z hz
    exact pred_le_choose_two (hfiber_pos z hz)
  rw [unorderedCollisionCount] at hsum
  have hrewrite :
      ∑ z ∈ S.image label, ((S.filter fun i ↦ label i = z).card - 1) =
        S.card - (S.image label).card := by
    rw [Finset.sum_tsub_distrib (S.image label) (fun z hz ↦ hfiber_pos z hz),
      sum_fiber_card_eq]
    simp
  rwa [hrewrite] at hsum

/-- The fiber second moment at a fixed parameter.  The right factor is the
index count plus twice the number of unordered colliding pairs. -/
theorem card_sq_le_image_card_mul_add_two_mul_unorderedCollisionCount
    (S : Finset Index) (label : Index → Label) :
    S.card ^ 2 ≤ (S.image label).card *
      (S.card + 2 * unorderedCollisionCount S label) := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := S.image label)
    (f := fun z ↦ ((S.filter fun i ↦ label i = z).card : ℝ))
  have hmass :
      (∑ z ∈ S.image label,
        ((S.filter fun i ↦ label i = z).card : ℝ)) = (S.card : ℝ) := by
    rw [← Nat.cast_sum, sum_fiber_card_eq]
  have hsquares :
      ∑ z ∈ S.image label, (S.filter fun i ↦ label i = z).card ^ 2 =
        S.card + 2 * unorderedCollisionCount S label := by
    rw [unorderedCollisionCount, ← sum_fiber_card_eq S label]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    exact sq_eq_add_two_mul_choose_two _
  rw [hmass] at hcs
  have hcast :
      (∑ z ∈ S.image label,
        ((S.filter fun i ↦ label i = z).card : ℝ) ^ 2) =
          (S.card + 2 * unorderedCollisionCount S label : ℕ) := by
    push_cast
    exact_mod_cast hsquares
  rw [hcast] at hcs
  exact_mod_cast hcs

/-- If the total unordered collision count over a nonempty parameter set is at
most `F`, one parameter simultaneously satisfies the paper's additive and
second-moment image bounds.

The second bound is the exact natural ceiling of
`H M² / (H M + 2F)`, where `H = P.card` and `M = S.card`.  In the empty-index
case both image bounds are zero. -/
theorem exists_parameter_image_card_bounds
    (P : Finset Parameter) (S : Finset Index)
    (label : Parameter → Index → Label) (F : ℕ)
    (hP : P.Nonempty)
    (htotal : ∑ p ∈ P, unorderedCollisionCount S (label p) ≤ F) :
    ∃ p ∈ P,
      S.card - F / P.card ≤ (S.image (label p)).card ∧
      natCeilDiv (P.card * S.card ^ 2)
          (P.card * S.card + 2 * F) ≤ (S.image (label p)).card := by
  classical
  have hPcard : 0 < P.card := Finset.card_pos.mpr hP
  have havg : ∃ p ∈ P, P.card * unorderedCollisionCount S (label p) ≤ F := by
    by_contra! hnone
    have hstrict :
        ∑ p ∈ P, F < ∑ p ∈ P, P.card * unorderedCollisionCount S (label p) :=
      Finset.sum_lt_sum_of_nonempty hP fun p hp ↦ hnone p hp
    have hleft : ∑ _p ∈ P, F = P.card * F := by simp [Nat.mul_comm]
    have hright :
        ∑ p ∈ P, P.card * unorderedCollisionCount S (label p) =
          P.card * ∑ p ∈ P, unorderedCollisionCount S (label p) := by
      rw [mul_sum]
    rw [hleft, hright] at hstrict
    exact (not_lt_of_ge (Nat.mul_le_mul_left P.card htotal)) hstrict
  obtain ⟨p, hp, hpavg⟩ := havg
  refine ⟨p, hp, ?_, ?_⟩
  · have hcollision : unorderedCollisionCount S (label p) ≤ F / P.card := by
      rw [Nat.le_div_iff_mul_le hPcard]
      simpa [Nat.mul_comm] using hpavg
    have hadd := card_sub_image_card_le_unorderedCollisionCount S (label p)
    omega
  · by_cases hS : S.card = 0
    · simp [hS, natCeilDiv]
    have hdenom : 0 < P.card * S.card + 2 * F := by positivity
    apply natCeilDiv_le_of_le_mul hdenom
    have hsecond :=
      card_sq_le_image_card_mul_add_two_mul_unorderedCollisionCount S (label p)
    calc
      P.card * S.card ^ 2 ≤
          P.card * ((S.image (label p)).card *
            (S.card + 2 * unorderedCollisionCount S (label p))) :=
        Nat.mul_le_mul_left P.card hsecond
      _ = (S.image (label p)).card *
          (P.card * S.card + 2 *
            (P.card * unorderedCollisionCount S (label p))) := by
        simp only [Nat.mul_add]
        ac_rfl
      _ ≤ (S.image (label p)).card * (P.card * S.card + 2 * F) := by
        exact Nat.mul_le_mul_left _
          (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpavg) _)

/-- At the same parameter supplied by collision averaging, deleting challenge zero
loses at most one value from each image lower bound. -/
theorem exists_parameter_nonzero_image_card_bounds
    [Zero Label]
    (P : Finset Parameter) (S : Finset Index)
    (label : Parameter → Index → Label) (F : ℕ)
    (hP : P.Nonempty)
    (htotal : ∑ p ∈ P, unorderedCollisionCount S (label p) ≤ F) :
    ∃ p ∈ P,
      S.card - F / P.card - 1 ≤
        ((S.image (label p)).filter fun z ↦ z ≠ 0).card ∧
      natCeilDiv (P.card * S.card ^ 2)
          (P.card * S.card + 2 * F) - 1 ≤
        ((S.image (label p)).filter fun z ↦ z ≠ 0).card := by
  classical
  obtain ⟨p, hp, hadd, hsecond⟩ :=
    exists_parameter_image_card_bounds P S label F hP htotal
  refine ⟨p, hp, ?_, ?_⟩
  · have herase :
        (S.image (label p)).filter (fun z ↦ z ≠ 0) =
          (S.image (label p)).erase 0 := by
      ext z
      simp [and_comm]
    rw [herase]
    by_cases hzero : 0 ∈ S.image (label p)
    · rw [Finset.card_erase_of_mem hzero]
      omega
    · rw [Finset.erase_eq_self.mpr hzero]
      omega
  · have herase :
        (S.image (label p)).filter (fun z ↦ z ≠ 0) =
          (S.image (label p)).erase 0 := by
      ext z
      simp [and_comm]
    rw [herase]
    by_cases hzero : 0 ∈ S.image (label p)
    · rw [Finset.card_erase_of_mem hzero]
      omega
    · rw [Finset.erase_eq_self.mpr hzero]
      omega

end BinaryFieldCounterexamples
