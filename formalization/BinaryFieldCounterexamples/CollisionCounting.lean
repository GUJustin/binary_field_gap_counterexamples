/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import ArkLib.ToMathlib.Finset.Basic
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Counting distinct challenges from bounded collisions

A family of witnesses does not by itself count distinct exceptional challenges. These lemmas
separate the witness population, the map to challenges, and the bound on each fiber.
The statements are independent of characteristic and of the polynomial construction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

variable {Witness Challenge : Type*} [DecidableEq Challenge]

/-- If every challenge has at most `B` witnesses, there are at least `|S| / B`
distinct challenges, expressed without rounding or a positivity hypothesis. -/
theorem card_le_card_image_mul_of_fiber_le
    (S : Finset Witness) (challenge : Witness → Challenge) (B : ℕ)
    (hfiber : ∀ z ∈ S.image challenge,
      (S.filter fun w ↦ challenge w = z).card ≤ B) :
    S.card ≤ (S.image challenge).card * B := by
  by_contra! h
  obtain ⟨z, hz, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (fun w hw ↦ Finset.mem_image.mpr ⟨w, hw, rfl⟩) h
  exact (not_lt_of_ge (hfiber z hz)) hlarge

/-- A bounded-collision witness family contained in a bad event gives a lower bound
on the size of that event. Membership and collision control are separate hypotheses. -/
theorem card_le_card_bad_mul_of_witnesses
    (S : Finset Witness) (bad : Finset Challenge) (challenge : Witness → Challenge) (B : ℕ)
    (hbad : ∀ w ∈ S, challenge w ∈ bad)
    (hfiber : ∀ z ∈ bad, (S.filter fun w ↦ challenge w = z).card ≤ B) :
    S.card ≤ bad.card * B := by
  by_contra! h
  obtain ⟨z, hz, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hbad h
  exact (not_lt_of_ge (hfiber z hz)) hlarge

/-- The witness family proves that a proposed exceptional-set budget is too small
whenever the witness count exceeds that budget times the maximum collision count. -/
theorem budget_lt_card_bad_of_witnesses
    (S : Finset Witness) (bad : Finset Challenge) (challenge : Witness → Challenge)
    (B budget : ℕ)
    (hbad : ∀ w ∈ S, challenge w ∈ bad)
    (hfiber : ∀ z ∈ bad, (S.filter fun w ↦ challenge w = z).card ≤ B)
    (hcount : budget * B < S.card) :
    budget < bad.card := by
  have h := card_le_card_bad_mul_of_witnesses S bad challenge B hbad hfiber
  by_contra! hbudget
  exact (not_lt_of_ge (h.trans (Nat.mul_le_mul_right B hbudget))) hcount

end BinaryFieldCounterexamples
