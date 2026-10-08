/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionAveraging
/-!
# Collision pooling with an exact rational energy

Finite averaging chooses one parameter satisfying both the additive floor
bound and second-moment ceiling bound. Rational energy remains rational
throughout, including empty families and zero energy.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_parameter_image_card_rational_bounds
    {Parameter Index Label : Type*}
    (P : Finset Parameter) (S : Finset Index) (label : Parameter → Index → Label)
    (E : ℚ) (hP : P.Nonempty)
    (htotal : (∑ p ∈ P, (unorderedCollisionCount S (label p) : ℚ))≤E) :
    ∃ p ∈ P,
      max (S.card-⌊E/P.card⌋₊)
        ⌈(P.card : ℚ)*S.card^2/(P.card*S.card+2*E)⌉₊≤(S.image (label p)).card := by
  classical
  have hp : (0 : ℚ)<P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hE : 0≤E := le_trans (by positivity) htotal
  have hsums : (∑ p ∈ P, (P.card : ℚ)*unorderedCollisionCount S (label p))≤∑ _p ∈ P, E := by
    rw [←Finset.mul_sum]
    simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_left htotal hp.le
  obtain ⟨p,hpP,havg⟩ := Finset.exists_le_of_sum_le hP hsums
  refine ⟨p,hpP,max_le ?_ ?_⟩
  · have hc : unorderedCollisionCount S (label p)≤⌊E/P.card⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ hp).mpr
      simpa only [mul_comm] using havg
    have hadd := card_sub_image_card_le_unorderedCollisionCount S (label p)
    omega
  · apply Nat.ceil_le.mpr
    by_cases hz : S.card=0
    · simp [hz]
    have hs : (0 : ℚ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hd : (0 : ℚ)<P.card*S.card+2*E := by positivity
    apply (div_le_iff₀ hd).mpr
    have hsecond := card_sq_le_image_card_mul_add_two_mul_unorderedCollisionCount S (label p)
    have hsecond' : (S.card : ℚ)^2≤((S.image (label p)).card : ℚ)*
        (S.card+2*unorderedCollisionCount S (label p)) := by exact_mod_cast hsecond
    have hmul := mul_le_mul_of_nonneg_left hsecond' hp.le
    have himage : (0 : ℚ)≤(S.image (label p)).card := by positivity
    linarith [mul_le_mul_of_nonneg_left havg himage]
end BinaryFieldCounterexamples
