/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Numerator

/-!
# Transport and pole dependence of the canonical numerator

The inverse-Frobenius numerator commutes with field embeddings, and changing
the exterior pole changes only its constant term. These facts align the common
head of a base-field locator family with the extension-field first-input bound.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq

/-- The canonical numerator commutes with an embedding of finite fields. -/
theorem map_primePowerQuarterNumerator
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B→+*F) (p r : ℕ) [Fact p.Prime] [CharP B p] [CharP F p]
    (hr : 1≤r) (L : B[X]) (β : B)
    (hs : ∀ n∈L.support,∃i : ℕ,n=(p^r)^i) :
    (primePowerQuarterNumerator p r L β).map φ=
      primePowerQuarterNumerator p r (L.map φ) (φ β) := by
  let A := (primePowerQuarterNumerator p r L β).map φ
  let C := primePowerQuarterNumerator p r (L.map φ) (φ β)
  have hsmap : ∀ n∈(L.map φ).support,∃i : ℕ,n=(p^r)^i := by
    intro n hn
    apply hs n
    rw [mem_support_iff] at hn ⊢
    exact fun hz => hn (by simp [coeff_map,hz])
  have hApow : A^(p^r)=primePowerQuarterRadicand (L.map φ) (φ β) := by
    dsimp [A]
    rw [←Polynomial.map_pow φ]
    rw [primePowerQuarterNumerator_pow p r hr L β hs]
    simp [primePowerQuarterRadicand]
  have hCpow : C^(p^r)=primePowerQuarterRadicand (L.map φ) (φ β) :=
    primePowerQuarterNumerator_pow p r hr (L.map φ) (φ β) hsmap
  have hsubpow : (A-C)^(p^r)=0 := by
    rw [sub_pow_expChar_pow,hApow,hCpow,sub_self]
  have hsub : A-C=0 := eq_zero_of_pow_eq_zero hsubpow
  exact sub_eq_zero.mp hsub

/-- Changing the pole changes only the constant term of the canonical numerator. -/
theorem primePowerQuarterNumerator_sub_natDegree_le_zero
    {F : Type*} [Field F] [Fintype F]
    (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1≤r) (L : F[X]) (α β : F)
    (hs : ∀ n∈L.support,∃i : ℕ,n=(p^r)^i) :
    (primePowerQuarterNumerator p r L α-
      primePowerQuarterNumerator p r L β).natDegree≤0 := by
  let A := primePowerQuarterNumerator p r L α
  let B := primePowerQuarterNumerator p r L β
  have hpow : (A-B)^(p^r)=C (L.coeff 1*(α-β)) := by
    rw [sub_pow_expChar_pow,primePowerQuarterNumerator_pow p r hr L α hs,
      primePowerQuarterNumerator_pow p r hr L β hs]
    simp only [primePowerQuarterRadicand]
    rw [mul_sub,mul_sub]
    simp only [sub_sub_sub_cancel_left,←C_mul,←C_sub]
    congr 1
    ring
  have hp : 0<p^r := pow_pos (Fact.out : p.Prime).pos _
  by_cases hz : A-B=0
  · change (A-B).natDegree≤0
    rw [hz]
    simp
  have hd : (p^r)*(A-B).natDegree≤0 := by
    rw [←Polynomial.natDegree_pow,hpow]
    rw [Polynomial.natDegree_C]
  change (A-B).natDegree≤0
  by_contra hn
  have hpos : 0<(p^r)*(A-B).natDegree :=
    Nat.mul_pos hp (Nat.pos_of_ne_zero (by omega))
  omega

end BinaryFieldCounterexamples
