/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalRoots
public import Mathlib.Algebra.Polynomial.Splits
/-!
# Existence of quadratic locator factors

A saturated Frobenius root set gives splitting. Exact root multiplicities then
supply polynomial divisibility, and the differential identity constructs actual
factors satisfying the locator conversion identity. No population is assumed.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- A saturated zero set of a Frobenius-supported polynomial proves splitting over the actual field. -/
theorem splits_of_primePower_full_card
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) (hP : P≠0) (S : Finset F)
    (hs : ∀ n∈P.support,p^r ∣ n)
    (hzero : ∀ x∈S,P.eval x=0) (hd : P.natDegree≤p^r*S.card) : P.Splits := by
  classical
  let A := primePowerPolynomialRoot p r P
  have hpow : A^(p^r)=P := primePowerPolynomialRoot_pow p r P hs
  have hp : 0<p^r := pow_pos (Fact.out : p.Prime).pos _
  have hA : A≠0 := by intro hz; rw [←hpow,hz,zero_pow (by omega)] at hP; exact hP rfl
  have hAd : A.natDegree≤S.card := by
    rw [←hpow,natDegree_pow] at hd
    exact Nat.le_of_mul_le_mul_left hd hp
  have hAz : ∀ x∈S,A.eval x=0 := by
    intro x hx
    have he := hzero x hx
    rw [←hpow,eval_pow] at he
    exact (pow_eq_zero_iff (by omega)).mp he
  obtain ⟨hdeg,hroots,hm⟩ := roots_eq_and_simple_of_full_card A hA S hAz hAd
  have hAsplit : A.Splits := by
    apply splits_iff_card_roots.mpr
    have h1 : S.card≤A.roots.card := by
      rw [←hroots]
      exact Multiset.toFinset_card_le _
    have h2 := card_roots' A
    omega
  rw [←hpow]
  exact hAsplit.pow _

/-- A split polynomial divides any polynomial whose root multiplicities dominate its own. -/
theorem dvd_of_splits_multiplicity_le {F : Type*} [Field F] (A G : F[X])
    (hA : A≠0) (hs : A.Splits) (hm : ∀ x,rootMultiplicity x A≤rootMultiplicity x G) : A∣G := by
  classical
  apply hs.dvd_of_roots_le_roots hA
  rw [Multiset.le_iff_count]
  intro x
  simpa only [count_roots] using hm x
end BinaryFieldCounterexamples


namespace BinaryFieldCounterexamples
open Polynomial

/-- Construct actual Frobenius and quotient factors satisfying the common-head conversion identity. -/
theorem exists_converted_quadratic_factors {F : Type*} [Field F] [Fintype F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (G J L : F[X]) (lam : F)
    (hlam : lam≠0) (hJ : J≠0) (hJG : J∣G)
    (hs : ∀ e∈J.support,p^r ∣ e)
    (hd : G^(p^r)-G= -C (lam⁻¹)*L*J) :
    ∃ A P S : F[X], A≠0 ∧ G=A*P ∧ J= -C lam*A^(p^r) ∧
      G=J*S ∧ P^(p^r)=L-C lam*S := by
  classical
  let D := -C (lam⁻¹)*J
  let A := primePowerPolynomialRoot p r D
  have hp : 0<p^r := pow_pos (Fact.out : p.Prime).pos _
  have hD : D≠0 := mul_ne_zero (neg_ne_zero.mpr (C_ne_zero.mpr (inv_ne_zero hlam))) hJ
  have hDs : ∀ e∈D.support,p^r ∣ e := by
    intro e he
    apply hs e
    rw [mem_support_iff] at he ⊢
    dsimp [D] at he
    simp only [neg_mul,coeff_neg,coeff_C_mul,neg_ne_zero,mul_ne_zero_iff] at he
    exact he.2
  have hpow : A^(p^r)=D := primePowerPolynomialRoot_pow p r D hDs
  have hA : A≠0 := by intro hz; rw [←hpow,hz,zero_pow (by omega)] at hD; exact hD rfl
  have hJA : J= -C lam*A^(p^r) := by
    rw [hpow]
    dsimp [D]
    simp [←mul_assoc,←map_mul,hlam]
  have hAJ : A∣J := by
    rw [hJA]
    exact dvd_mul_of_dvd_right (dvd_pow_self A (by omega)) _
  obtain ⟨P,hP⟩ := dvd_trans hAJ hJG
  obtain ⟨S,hS⟩ := hJG
  refine ⟨A,P,S,hA,hP,hJA,hS,?_⟩
  apply mul_left_cancel₀ (show A^(p^r)≠0 from pow_ne_zero _ hA)
  have hh := hd
  rw [hP,mul_pow] at hh
  have hG : A*P= -C lam*A^(p^r)*S := by rw [←hP,←hJA]; exact hS
  rw [hG,hJA] at hh
  have hl : -C (lam⁻¹)*L*(-C lam*A^(p^r))=L*A^(p^r) := by
    calc
      _ = C (lam⁻¹*lam)*(L*A^(p^r)) := by rw [map_mul]; ring
      _ = _ := by simp [hlam]
  rw [hl] at hh
  linear_combination hh
end BinaryFieldCounterexamples
