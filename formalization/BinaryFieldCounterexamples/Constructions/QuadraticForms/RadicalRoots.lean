/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Numerator
public import BinaryFieldCounterexamples.Polynomial.QuadraticLocatorRoots
/-!
# Frobenius root bounds and exact multiplicities

Dividing a polynomial's sparse support by a prime power yields a concrete
Frobenius root and the corresponding bound on distinct roots. If a supplied
root set saturates this degree bound, it is the complete root set and each
original root has exactly the prime-power multiplicity. These algebraic facts
apply to the derivative's radical coset once that coset is constructed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.decEq

/-- Divisible support exponents divide the bound on the number of distinct roots. -/
theorem card_roots_le_of_primePower_support
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) (hP : P ≠ 0)
    (hs : ∀ n ∈ P.support, p^r ∣ n) (M : ℕ)
    (hd : P.natDegree ≤ p^r*M) :
    P.roots.toFinset.card ≤ M := by
  classical
  let A := primePowerPolynomialRoot p r P
  have hpow : A^(p^r) = P := primePowerPolynomialRoot_pow p r P hs
  have hp : 0 < p^r := pow_pos (Fact.out : p.Prime).pos _
  have hA : A ≠ 0 := by
    intro hz
    apply hP
    rw [← hpow, hz, zero_pow (by omega)]
  have hAdeg : A.natDegree ≤ M := by
    rw [← hpow, natDegree_pow] at hd
    exact Nat.le_of_mul_le_mul_left hd hp
  have he : P.roots.toFinset = A.roots.toFinset := by
    ext x
    simp only [Multiset.mem_toFinset, mem_roots hP, mem_roots hA, IsRoot.def]
    rw [← hpow, eval_pow]
    exact pow_eq_zero_iff (by omega)
  rw [he]
  exact (Multiset.toFinset_card_le _).trans ((card_roots' A).trans hAdeg)

/-- A derivative index gap gives the radical-size bound needed by the quadratic trace family. -/
theorem card_roots_le_of_qPower_index_interval
    {F : Type*} [Field F] [Fintype F] (p r t m : ℕ) [Fact p.Prime] [CharP F p]
    (htm : 2*t ≤ m) (P : F[X]) (hP : P ≠ 0)
    (hs : ∀ n ∈ P.support, n = 0 ∨ ∃ i : ℕ, t ≤ i ∧ n = (p^r)^i)
    (hd : P.natDegree ≤ (p^r)^(m-t)) :
    P.roots.toFinset.card ≤ (p^r)^(m-2*t) := by
  apply card_roots_le_of_primePower_support p (r*t) P hP
  · intro n hn
    rcases hs n hn with hz | ⟨i, hti, hi⟩
    · simp [hz]
    · rw [hi, ← pow_mul]
      exact pow_dvd_pow p (Nat.mul_le_mul_left r hti)
  · have he : p^(r*t)*(p^r)^(m-2*t) = (p^r)^(m-t) := by
      rw [pow_mul, ← pow_add]
      congr 1
      omega
    rw [he]
    exact hd

/-- Saturating the degree bound by distinct roots determines every root and its multiplicity. -/
theorem roots_eq_and_simple_of_full_card
    {F : Type*} [Field F] (P : F[X]) (hP : P ≠ 0) (S : Finset F)
    (hzero : ∀ x ∈ S, P.eval x = 0) (hd : P.natDegree ≤ S.card) :
    P.natDegree = S.card ∧ P.roots.toFinset = S ∧
      ∀ x ∈ S, rootMultiplicity x P = 1 := by
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (hzero x hx))
  have hc1 := Finset.card_le_card hsub
  have hc2 := Multiset.toFinset_card_le P.roots
  have hc3 := card_roots' P
  have hn : P.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
  refine ⟨by omega, (Finset.eq_of_subset_of_card_le hsub (by omega)).symm, ?_⟩
  intro x hx
  rw [← count_roots]
  exact Multiset.count_eq_one_of_mem hn (Multiset.mem_toFinset.mp (hsub hx))

/-- A full-size root set of a Frobenius power has exactly the asserted scaled multiplicities. -/
theorem primePower_root_multiplicity_of_full_card
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) (hP : P ≠ 0) (S : Finset F)
    (hs : ∀ n ∈ P.support, p^r ∣ n)
    (hzero : ∀ x ∈ S, P.eval x = 0) (hd : P.natDegree ≤ p^r*S.card) :
    P.natDegree = p^r*S.card ∧ P.roots.toFinset = S ∧
      ∀ x ∈ S, rootMultiplicity x P = p^r := by
  let A := primePowerPolynomialRoot p r P
  have hpow : A^(p^r) = P := primePowerPolynomialRoot_pow p r P hs
  have hp : 0 < p^r := pow_pos (Fact.out : p.Prime).pos _
  have hA : A ≠ 0 := by
    intro hz
    apply hP
    rw [← hpow, hz, zero_pow (by omega)]
  have hAdeg : A.natDegree ≤ S.card := by
    rw [← hpow, natDegree_pow] at hd
    exact Nat.le_of_mul_le_mul_left hd hp
  have hAzero : ∀ x ∈ S, A.eval x = 0 := by
    intro x hx
    have he := hzero x hx
    rw [← hpow, eval_pow] at he
    exact (pow_eq_zero_iff (by omega)).mp he
  obtain ⟨hdegree, hroots, hsimple⟩ := roots_eq_and_simple_of_full_card A hA S hAzero hAdeg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hpow, natDegree_pow, hdegree]
  · rw [← hroots]
    ext x
    simp only [Multiset.mem_toFinset, mem_roots hP, mem_roots hA, IsRoot.def]
    rw [← hpow, eval_pow]
    exact pow_eq_zero_iff (by omega)
  · intro x hx
    rw [← hpow, QuadraticLocatorConversion.rootMultiplicity_power A hA,
      hsimple x hx, mul_one]

/-- Known roots with an extra multiplicity on a subset give a weighted degree lower bound. -/
theorem weighted_root_card_le_natDegree
    {F : Type*} [Field F] (P : F[X]) (hP : P ≠ 0) (S R : Finset F)
    (hRS : R ⊆ S) (e : ℕ) (hzero : ∀ x ∈ S, P.eval x = 0)
    (hmult : ∀ x ∈ R, e+1 ≤ rootMultiplicity x P) :
    S.card + e*R.card ≤ P.natDegree := by
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (hzero x hx))
  have hsum : ∑ x ∈ S, rootMultiplicity x P ≤ P.natDegree := by
    calc
      _ ≤ ∑ x ∈ P.roots.toFinset, rootMultiplicity x P :=
        Finset.sum_le_sum_of_subset hsub
      _ = P.roots.card := by
        simp only [← count_roots]
        exact Multiset.toFinset_sum_count_eq _
      _ ≤ _ := card_roots' P
  have hlower : ∑ x ∈ S, (1 + if x ∈ R then e else 0) ≤ ∑ x ∈ S, rootMultiplicity x P := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases hxR : x ∈ R
    · simpa [hxR, Nat.add_comm] using hmult x hxR
    · simp only [hxR, ite_false, add_zero]
      exact (rootMultiplicity_pos hP).mpr (hzero x hx)
  have heq : ∑ x ∈ S, (1 + if x ∈ R then e else 0) = S.card + e*R.card := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hRS, Nat.mul_comm]
  rw [heq] at hlower
  exact hlower.trans hsum


end BinaryFieldCounterexamples
