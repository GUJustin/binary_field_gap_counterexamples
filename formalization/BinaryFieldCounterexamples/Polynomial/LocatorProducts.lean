/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
/-!
# Leading coefficient gaps in locator products

Actual binary subgroup and affine-flat locators have half-size leading gaps.
Multiplying factors preserves the common leading monomial and loses at least
the smallest gap whenever a nonleading term is used.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial BinaryLocator
open scoped BigOperators

theorem natDegree_prod_sub_power_le
    {ι F : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (P : ι → F[X]) (L m : ℕ) (hm : m≤L)
    (hdeg : ∀ i ∈ s, (P i).natDegree≤L)
    (htail : ∀ i ∈ s, (P i-X^L).natDegree≤L-m) :
    ((∏ i ∈ s, P i)-X^(s.card*L)).natDegree≤s.card*L-m := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases hs : s=∅
    · subst s
      simpa using htail a (by simp)
    have hds : ∀ i ∈ s, (P i).natDegree≤L := fun i hi => hdeg i (Finset.mem_insert_of_mem hi)
    have hts : ∀ i ∈ s, (P i-X^L).natDegree≤L-m := fun i hi => htail i (Finset.mem_insert_of_mem hi)
    have hh := ih hds hts
    have hprod : (∏ i ∈ s, P i).natDegree≤s.card*L := by
      apply (natDegree_prod_le (s := s) (f := P)).trans
      simpa using Finset.sum_le_sum hds
    have hn : 1≤s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have hm' : m≤s.card*L := hm.trans (Nat.le_mul_of_pos_left L hn)
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha]
    have he : P a*(∏ i ∈ s, P i)-X^((s.card+1)*L) =
        (P a-X^L)*(∏ i ∈ s, P i)+X^L*((∏ i ∈ s, P i)-X^(s.card*L)) := by
      rw [Nat.add_mul,Nat.one_mul,pow_add]
      ring
    rw [he]
    rw [Nat.add_mul,Nat.one_mul]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hpa := htail a (Finset.mem_insert_self a s)
      omega
    · apply natDegree_mul_le.trans
      rw [natDegree_X_pow]
      omega

theorem subspacePolynomial_sub_leading_natDegree_le
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (m : ℕ) (hcard : Fintype.card W=2^(m+1)) :
    (subspacePolynomial W-X^(2^(m+1))).natDegree≤2^m := by
  have hd : (subspacePolynomial W).natDegree=2^(m+1) := by simp [hcard]
  have hc : (subspacePolynomial W).coeff (2^(m+1))=1 := by
    rw [←hd]
    exact (subspacePolynomial_monic W).coeff_natDegree
  have he := monomial_add_erase (subspacePolynomial W) (2^(m+1))
  rw [hc,←C_mul_X_pow_eq_monomial,C_1,one_mul] at he
  have ht : subspacePolynomial W-X^(2^(m+1))=(subspacePolynomial W).erase (2^(m+1)) := by
    linear_combination -he
  rw [ht]
  have hs : IsBinaryLinearized (subspacePolynomial W) := subspacePolynomial_support W
  exact hs.natDegree_erase_le m hd.le
theorem affine_subspacePolynomial_sub_leading_natDegree_le
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (a : F) (m : ℕ) (hcard : Fintype.card W=2^(m+1)) :
    ((subspacePolynomial W).comp (X-C a)-X^(2^(m+1))).natDegree≤2^m := by
  have he : (subspacePolynomial W).comp (X-C a)=
      subspacePolynomial W+C ((subspacePolynomial W).eval (-a)) := by
    simpa only [sub_eq_add_neg,map_neg] using subspacePolynomial_comp_X_add_C W (-a)
  rw [he]
  have hr : subspacePolynomial W+C ((subspacePolynomial W).eval (-a))-X^(2^(m+1))=
      (subspacePolynomial W-X^(2^(m+1)))+C ((subspacePolynomial W).eval (-a)) := by ring
  rw [hr]
  exact (natDegree_add_le _ _).trans (max_le
    (subspacePolynomial_sub_leading_natDegree_le W m hcard) (by simp))
end BinaryFieldCounterexamples
