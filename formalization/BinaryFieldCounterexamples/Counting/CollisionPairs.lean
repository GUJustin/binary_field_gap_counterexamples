/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.CollisionAveraging
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sigma
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Collision budgets from pairwise uniqueness

This file turns the statement that each distinct pair of indices can collide
at at most one parameter into the total unordered-collision budget used by
collision averaging.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Finset

variable {Index Parameter Label : Type*} [DecidableEq Label]

/-- Unordered fiber collisions are precisely the strictly ordered pairs (for
an arbitrary linear order) having equal labels. -/
theorem unorderedCollisionCount_eq_card_pairCollisions
    [LinearOrder Index] (S : Finset Index) (label : Index → Label) :
    unorderedCollisionCount S label =
      ((S ×ˢ S).filter fun ij ↦ ij.1 < ij.2 ∧ label ij.1 = label ij.2).card := by
  classical
  let fibers : Label → Finset Index := fun z ↦ S.filter fun i ↦ label i = z
  let aPairs := (S.image label).sigma fun z ↦
    ((fibers z ×ˢ fibers z).filter fun ij ↦ ij.1 < ij.2)
  let tPairs := (S ×ˢ S).filter fun ij ↦ ij.1 < ij.2 ∧ label ij.1 = label ij.2
  have hAcard : aPairs.card = unorderedCollisionCount S label := by
    simp only [aPairs, Finset.card_sigma]
    simp_rw [Finset.card_product_filter_lt]
    rfl
  rw [← hAcard]
  apply Finset.card_bij (fun a _ ↦ a.2)
  · rintro ⟨z, ij⟩ ha
    rw [Finset.mem_sigma] at ha
    rcases ha with ⟨hz, hij⟩
    rw [Finset.mem_filter, Finset.mem_product] at hij
    rcases hij with ⟨⟨hi, hj⟩, hij⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hj).1⟩,
      hij, (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm⟩
  · rintro ⟨z₁, ij₁⟩ h₁ ⟨z₂, ij₂⟩ h₂ hij
    simp only at hij
    subst ij₂
    rw [Finset.mem_sigma] at h₁ h₂
    have hi₁ := (Finset.mem_filter.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp h₁.2).1).1).2
    have hi₂ := (Finset.mem_filter.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp h₂.2).1).1).2
    have hz : z₁ = z₂ := hi₁.symm.trans hi₂
    subst z₂
    rfl
  · intro ij hij
    rw [Finset.mem_filter, Finset.mem_product] at hij
    rcases hij with ⟨⟨hi, hj⟩, hlt, heq⟩
    let a : Sigma fun _ : Label ↦ Index × Index := ⟨label ij.1, ij⟩
    have ha : a ∈ aPairs := by
      simp only [aPairs, Finset.mem_sigma]
      refine ⟨Finset.mem_image.mpr ⟨ij.1, hi, rfl⟩, ?_⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_filter.mpr ⟨hi, rfl⟩,
        Finset.mem_filter.mpr ⟨hj, heq.symm⟩⟩, hlt⟩
    exact ⟨a, ha, rfl⟩

/-- If each distinct index pair collides at at most one parameter, the total
number of unordered collisions is at most the number of unordered pairs. -/
theorem sum_unorderedCollisionCount_le_choose_two
    [LinearOrder Index]
    (P : Finset Parameter) (S : Finset Index)
    (label : Parameter → Index → Label)
    (hunique : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ((P.filter fun p ↦ label p i = label p j).card ≤ 1)) :
    ∑ p ∈ P, unorderedCollisionCount S (label p) ≤ S.card.choose 2 := by
  classical
  let pairs := (S ×ˢ S).filter fun ij ↦ ij.1 < ij.2
  calc
    ∑ p ∈ P, unorderedCollisionCount S (label p) =
        ∑ p ∈ P, (pairs.filter fun ij ↦ label p ij.1 = label p ij.2).card := by
      apply Finset.sum_congr rfl
      intro p _
      rw [unorderedCollisionCount_eq_card_pairCollisions]
      congr 1
      ext ij
      simp only [pairs, Finset.mem_filter, Finset.mem_product]
      tauto
    _ = ∑ ij ∈ pairs, (P.filter fun p ↦ label p ij.1 = label p ij.2).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _ij ∈ pairs, 1 := by
      apply Finset.sum_le_sum
      intro ij hij
      change ij ∈ (S ×ˢ S).filter (fun ij ↦ ij.1 < ij.2) at hij
      rcases Finset.mem_filter.mp hij with ⟨hijS, hijlt⟩
      rcases Finset.mem_product.mp hijS with ⟨hi, hj⟩
      exact hunique ij.1 hi ij.2 hj (ne_of_lt hijlt)
    _ = S.card.choose 2 := by
      simp [pairs, Finset.card_product_filter_lt]

end BinaryFieldCounterexamples
