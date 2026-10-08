/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.BinarySupport
public import Mathlib.FieldTheory.Separable

/-!
# Sparse locator tails and Frobenius remainders

The powers-of-two support of a binary locator gives strict gaps between its
leading terms. These gaps are used both in the codimension-two witnesses and
in the construction of simultaneous agreement for both inputs. Separability supplies
the nonzero linear coefficient needed by the upper bound on the first input.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial BinaryLocator

/-- A subgroup product has distinct roots, so it is separable over its field. -/
theorem subspacePolynomial_separable
    {F : Type*} [Field F] (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).Separable := by
  classical
  exact separable_prod_X_sub_C_iff.mpr Subtype.val_injective

/-- The coefficient of `X` in a subgroup locator is nonzero, in any characteristic. -/
theorem subspacePolynomial_coeff_one_ne_zero
    {F : Type*} [Field F] (W : AddSubgroup F) [Fintype W] :
    (subspacePolynomial W).coeff 1 ≠ 0 := by
  have hz : (subspacePolynomial W).eval₂ (RingHom.id F) 0 = 0 :=
    (subspacePolynomial_eval_eq_zero_iff W 0).mpr W.zero_mem
  have hd := (subspacePolynomial_separable W).eval₂_derivative_ne_zero (RingHom.id F) hz
  simpa only [eval₂_id, ← coeff_zero_eq_eval_zero, coeff_derivative,
    Nat.zero_add, Nat.cast_zero, zero_add, Nat.cast_one, mul_one] using hd

namespace BinaryLocator

/-- Removing one coefficient preserves power-of-two support. -/
theorem IsBinaryLinearized.erase
    {F : Type*} [Field F] {P : F[X]} (hP : IsBinaryLinearized P) (n : ℕ) :
    IsBinaryLinearized (P.erase n) := by
  intro j hj
  rw [support_erase] at hj
  exact hP j (Finset.mem_of_mem_erase hj)

/-- A binary-supported polynomial bounded by `2^(m+1)` drops to degree at most
`2^m` after removal of the coefficient at `2^(m+1)`, even if it was already zero. -/
theorem IsBinaryLinearized.natDegree_erase_le
    {F : Type*} [Field F] {P : F[X]} (hP : IsBinaryLinearized P)
    (m : ℕ) (hdeg : P.natDegree ≤ 2 ^ (m + 1)) :
    (P.erase (2 ^ (m + 1))).natDegree ≤ 2 ^ m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = 2 ^ (m + 1)
  · simp [heq]
  rw [erase_ne _ heq]
  by_contra hne
  obtain ⟨i, rfl⟩ := hP n (mem_support_iff.mpr hne)
  have hi : i ≤ m + 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((le_natDegree_of_ne_zero hne).trans hdeg)
  have him : m < i := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hn
  have : i = m + 1 := by omega
  exact heq (congrArg (2 ^ ·) this)

/-- Every binary-supported polynomial has zero constant term. -/
theorem IsBinaryLinearized.coeff_zero
    {F : Type*} [Field F] {P : F[X]} (hP : IsBinaryLinearized P) : P.coeff 0 = 0 := by
  by_contra hn
  obtain ⟨i, hi⟩ := hP 0 (mem_support_iff.mpr hn)
  exact (Nat.two_pow_pos i).ne' hi.symm

/-- Vanishing of the top coefficient strengthens the degree bound by the
binary support gap. -/
theorem IsBinaryLinearized.natDegree_le_of_top_coeff_zero
    {F : Type*} [Field F] {P : F[X]} (hP : IsBinaryLinearized P)
    (m : ℕ) (hdeg : P.natDegree ≤ 2 ^ (m + 1))
    (hc : P.coeff (2 ^ (m + 1)) = 0) : P.natDegree ≤ 2 ^ m := by
  have he : P.erase (2 ^ (m + 1)) = P := by
    simpa only [hc, map_zero, zero_add] using monomial_add_erase P (2 ^ (m + 1))
  rw [← he]
  exact hP.natDegree_erase_le m hdeg

end BinaryLocator

/-- Removing the leading three supported degrees gives the precise sparse
locator shape used for codimension-two subspaces. Its natural-degree bound
includes the zero tail, and the constant term remains zero. -/
theorem subspacePolynomial_three_term_shape
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (m : ℕ)
    (hcard : Fintype.card W = 2 ^ (m + 3)) :
    ∃ V : F[X], V.natDegree ≤ 2 ^ m ∧ V.coeff 0 = 0 ∧
      subspacePolynomial W = X ^ (2 ^ (m + 3)) +
        C ((subspacePolynomial W).coeff (2 ^ (m + 2))) * X ^ (2 ^ (m + 2)) +
        C ((subspacePolynomial W).coeff (2 ^ (m + 1))) * X ^ (2 ^ (m + 1)) + V := by
  let P := subspacePolynomial W
  let P₁ := P.erase (2 ^ (m + 3))
  let P₂ := P₁.erase (2 ^ (m + 2))
  let V := P₂.erase (2 ^ (m + 1))
  have hs : IsBinaryLinearized P := subspacePolynomial_support W
  have hs₁ : IsBinaryLinearized P₁ := hs.erase _
  have hs₂ : IsBinaryLinearized P₂ := hs₁.erase _
  have hsV : IsBinaryLinearized V := hs₂.erase _
  have hdeg : P.natDegree = 2 ^ (m + 3) := (subspacePolynomial_natDegree W).trans hcard
  have h₁ : P₁.natDegree ≤ 2 ^ (m + 2) := hs.natDegree_erase_le (m + 2) hdeg.le
  have h₂ : P₂.natDegree ≤ 2 ^ (m + 1) := hs₁.natDegree_erase_le (m + 1) h₁
  refine ⟨V, hs₂.natDegree_erase_le m h₂, hsV.coeff_zero, ?_⟩
  have h12 : 2 ^ (m + 1) < 2 ^ (m + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have h23 : 2 ^ (m + 2) < 2 ^ (m + 3) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hc : P.coeff (2 ^ (m + 3)) = 1 := by
    rw [← hdeg]
    exact (subspacePolynomial_monic W).coeff_natDegree
  have hP := (monomial_add_erase P (2 ^ (m + 3))).symm
  have hP₁ : P₁ = monomial (2 ^ (m + 2)) (P₁.coeff (2 ^ (m + 2))) + P₂ :=
    (monomial_add_erase P₁ (2 ^ (m + 2))).symm
  have hP₂ : P₂ = monomial (2 ^ (m + 1)) (P₂.coeff (2 ^ (m + 1))) + V :=
    (monomial_add_erase P₂ (2 ^ (m + 1))).symm
  have hc₁ : P₁.coeff (2 ^ (m + 2)) = P.coeff (2 ^ (m + 2)) :=
    erase_ne P h23.ne
  have hc₂ : P₂.coeff (2 ^ (m + 1)) = P.coeff (2 ^ (m + 1)) := by
    simp only [P₂, P₁, coeff_erase, ite_eq_right h12.ne, ite_eq_right (h12.trans h23).ne]
  change P = _
  calc
    P = monomial (2 ^ (m + 3)) (P.coeff (2 ^ (m + 3))) + P₁ := hP
    _ = X ^ (2 ^ (m + 3)) +
        C (P.coeff (2 ^ (m + 2))) * X ^ (2 ^ (m + 2)) +
        C (P.coeff (2 ^ (m + 1))) * X ^ (2 ^ (m + 1)) + V := by
      rw [hP₁, hP₂, hc, hc₁, hc₂]
      simp only [← C_mul_X_pow_eq_monomial, C_1, one_mul]
      ring

/-- Every iterated Frobenius monomial has a binary-supported representative
of degree at most half the subgroup size on the subgroup. In particular
`j = 0, 1, 2` gives the three simultaneous witnesses needed for common
agreement. Zero constant term follows from the explicitly included support
condition. -/
theorem subspacePolynomial_exists_frobenius_remainder
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (m : ℕ)
    (hcard : Fintype.card W = 2 ^ (m + 1)) (j : ℕ) :
    ∃ R : F[X], IsBinaryLinearized R ∧ R.natDegree ≤ 2 ^ m ∧
      R.coeff 0 = 0 ∧ ∀ x : W, R.eval (x : F) = (x : F) ^ (2 ^ (m + 1 + j)) := by
  let L := subspacePolynomial W
  have hs : IsBinaryLinearized L := subspacePolynomial_support W
  have hdeg : L.natDegree = 2 ^ (m + 1) := (subspacePolynomial_natDegree W).trans hcard
  have hcoeff : L.coeff (2 ^ (m + 1)) = 1 := by
    rw [← hdeg]
    exact (subspacePolynomial_monic W).coeff_natDegree
  have hroot (x : W) : L.eval (x : F) = 0 :=
    (subspacePolynomial_eval_eq_zero_iff W (x : F)).mpr x.property
  induction j with
  | zero =>
    let R := L.erase (2 ^ (m + 1))
    have hsR : IsBinaryLinearized R := hs.erase _
    refine ⟨R, hsR, hs.natDegree_erase_le m hdeg.le, hsR.coeff_zero, ?_⟩
    intro x
    have he := congrArg (fun p : F[X] ↦ p.eval (x : F))
      (monomial_add_erase L (2 ^ (m + 1)))
    rw [eval_add, hcoeff, eval_monomial, one_mul, hroot] at he
    have := eq_neg_of_add_eq_zero_right he
    simpa only [CharTwo.neg_eq, Nat.add_zero] using this
  | succ j ih =>
    obtain ⟨P, hsP, hdP, _, heP⟩ := ih
    let R := P ^ 2 - C (P.coeff (2 ^ m) ^ 2) * L
    have hsR : IsBinaryLinearized R := is_binary_linearized_sub _ _
      (is_binary_linearized_sq _ hsP) (is_binary_linearized_c_mul _ _ hs)
    have htw : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
    have hRdegree : R.natDegree ≤ 2 ^ (m + 1) := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · rw [htw]
        exact natDegree_pow_le_of_le 2 hdP
      · exact (natDegree_C_mul_le _ L).trans hdeg.le
    have hRcoeff : R.coeff (2 ^ (m + 1)) = 0 := by
      simp only [R, coeff_sub, coeff_C_mul, hcoeff, mul_one]
      rw [htw, coeff_pow_of_natDegree_le hdP, sub_self]
    refine ⟨R, hsR, hsR.natDegree_le_of_top_coeff_zero m hRdegree hRcoeff,
      hsR.coeff_zero, ?_⟩
    intro x
    simp only [R, eval_sub, eval_pow, eval_mul, eval_C, hroot, mul_zero, sub_zero, heP]
    rw [← pow_mul]
    congr 1

end BinaryFieldCounterexamples
