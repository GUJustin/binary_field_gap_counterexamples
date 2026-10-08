/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.QuotientLocator
/-!
# The fixed Gold polynomial and exact low-degree tails

All locators share the same two leading terms. Squaring this fixed polynomial
recovers the top two terms of the domain locator, whose remaining binary
support is at most quarter degree. The squared quotient identity then
forces the exact degree of the remaining tail.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]
/-- The two fixed leading terms shared by all Gold locators for the prescribed domain. -/
noncomputable def goldSourcePolynomial (D : AddSubgroup B) [Fintype D] (k : ℕ) : B[X] :=
  X^(2^k) + C ((frobeniusEquiv B 2).symm ((subspacePolynomial D).coeff (2^k))) * X^(2^(k-1))
/-- Squaring the fixed Gold polynomial recovers the two leading terms of the domain locator. -/
theorem goldSourcePolynomial_sq (D : AddSubgroup B) [Fintype D] (k : ℕ) (hk : 1 ≤ k) :
    goldSourcePolynomial D k ^ 2 = X^(2^(k+1)) +
      C ((subspacePolynomial D).coeff (2^k))*X^(2^k) := by
  rw [goldSourcePolynomial, CharTwo.add_sq, mul_pow, ← pow_mul, ← pow_mul, ← pow_succ,
    ← pow_succ, ← map_pow, frobeniusEquiv_symm_pow_p]
  have he : k-1+1=k := by omega
  rw [he]
/-- The domain locator differs from the squared fixed polynomial by a quarter-degree tail. -/
theorem subspacePolynomial_gold_tail (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hk : 1 ≤ k) (hD : Nat.card D = 2^(k+1)) :
    ∃ V : B[X], V.natDegree ≤ 2^(k-1) ∧
      subspacePolynomial D = goldSourcePolynomial D k ^ 2 + V := by
  let P := subspacePolynomial D
  let P₁ := P.erase (2^(k+1))
  let V := P₁.erase (2^k)
  have hs : BinaryLocator.IsBinaryLinearized P := subspacePolynomial_support D
  have hd : P.natDegree=2^(k+1) := by
    rw [subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hD]
  have h₁ : P₁.natDegree ≤ 2^k := hs.natDegree_erase_le k hd.le
  have he : k-1+1=k := by omega
  have h₂ : V.natDegree ≤ 2^(k-1) := by
    simpa only [he] using (hs.erase (2^(k+1))).natDegree_erase_le (k-1) (by simpa only [he] using h₁)
  refine ⟨V, h₂, ?_⟩
  have hc : P.coeff (2^(k+1))=1 := by rw [← hd]; exact (subspacePolynomial_monic D).coeff_natDegree
  have hlt : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hc₁ : P₁.coeff (2^k)=P.coeff (2^k) := erase_ne P hlt.ne
  rw [goldSourcePolynomial_sq D k hk]
  change P = _
  calc
    P = monomial (2^(k+1)) (P.coeff (2^(k+1)))+P₁ := (monomial_add_erase P _).symm
    _ = monomial (2^(k+1)) (P.coeff (2^(k+1)))+
      (monomial (2^k) (P₁.coeff (2^k))+V) := by congr 1; exact (monomial_add_erase P₁ _).symm
    _ = _ := by rw [hc, hc₁]; simp only [← C_mul_X_pow_eq_monomial, C_1, one_mul]; ring
/-- Subtracting the fixed polynomial leaves exactly half the discarded quotient degree. -/
theorem gold_locator_tail_natDegree (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hk : 1 ≤ k) (hD : Nat.card D = 2^(k+1)) (P Q : B[X])
    (hPQ : P^2=subspacePolynomial D+Q) (hQ : 2^(k-1)<Q.natDegree) :
    (P+goldSourcePolynomial D k).natDegree = Q.natDegree/2 := by
  obtain ⟨V, hV, hL⟩ := subspacePolynomial_gold_tail D k hk hD
  have he : (P+goldSourcePolynomial D k)^2=V+Q := by
    rw [CharTwo.add_sq, hPQ, hL]
    linear_combination (norm := ring_nf)
      goldSourcePolynomial D k ^ 2 * (CharTwo.two_eq_zero (R := B[X]))
  have hd := congrArg natDegree he
  rw [natDegree_pow, natDegree_add_eq_right_of_natDegree_lt (hV.trans_lt hQ)] at hd
  omega
end BinaryFieldCounterexamples.Gold
