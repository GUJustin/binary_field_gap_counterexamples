/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Ring.Parity
/-!
# Binary fields have no nontrivial power-of-two multiplicative domains

The unnumbered observation in Section 1, lines 57--59, explains why smooth
multiplicative domains of power-of-two size do not exist in binary fields.
The field cardinality is derived from characteristic two; it is not an extra
hypothesis. Lagrange's theorem then forces a multiplicative subgroup of size
`2^k` to have `k=0` and to be the trivial subgroup.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- Section 1, lines 57--59: the multiplicative group of every finite field
of characteristic two has odd order. -/
theorem prose_binary_unit_group_odd
    (F : Type*) [Field F] [Fintype F] [CharP F 2] : Odd (Nat.card Fˣ) := by
  classical
  obtain ⟨m, _, hcard⟩ := FiniteField.card F 2
  have heven : Even (Fintype.card F) := by
    rw [hcard]
    exact Nat.even_pow.mpr ⟨by decide, m.pos.ne'⟩
  have hmod := Nat.even_iff.mp heven
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  rw [Nat.odd_iff, Nat.card_eq_fintype_card, Fintype.card_units]
  omega

/-- Section 1, lines 57--59: a multiplicative subgroup of a binary field
with cardinality `2^k` must have exponent `k=0`. -/
theorem prose_binary_multiplicative_subgroup_power_two_exponent
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (H : Subgroup Fˣ) (k : ℕ) (hH : Nat.card H = 2^k) : k = 0 := by
  have hodd := prose_binary_unit_group_odd F
  have hdiv : 2^k ∣ Nat.card Fˣ := by
    simpa only [hH] using H.card_subgroup_dvd_card
  by_contra hk
  have heven : Even (2^k) := Nat.even_pow.mpr ⟨by decide, hk⟩
  exact hodd.not_two_dvd_nat (heven.two_dvd.trans hdiv)

/-- Section 1, lines 57--59: every multiplicative subgroup of power-of-two
size in a binary field is trivial, so it cannot be a nontrivial smooth domain. -/
theorem prose_binary_multiplicative_subgroup_power_two_trivial
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (H : Subgroup Fˣ) (k : ℕ) (hH : Nat.card H = 2^k) : H = ⊥ := by
  have hk := prose_binary_multiplicative_subgroup_power_two_exponent H k hH
  apply H.eq_bot_of_card_eq
  simpa only [hk, pow_zero] using hH

end BinaryFieldCounterexamples
