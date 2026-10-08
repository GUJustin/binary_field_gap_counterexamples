/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
public import BinaryFieldCounterexamples.Polynomial.DivX
public import BinaryFieldCounterexamples.Agreement.Basic

/-!
# Polynomial witnesses for the quadratic construction

The same pair of monomial words is fixed throughout. Subgroup locators produce
exceptional-challenge explaining polynomials, and the smaller-subgroup remainders
produce two simultaneous explaining polynomials on all nonzero subgroup coordinates.
The construction uses actual polynomial evaluations with strict message degrees.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

namespace QuadraticConstruction

/-- The first unshifted input of the quadratic construction. -/
def firstWord {F : Type*} [Field F] (K : ℕ) (θ : F) (x : F) : F :=
  x ^ (8 * K - 1) + θ * x ^ (4 * K - 1)

/-- The second input of the quadratic construction. -/
def secondWord {F : Type*} [Field F] (K : ℕ) (x : F) : F :=
  x ^ (2 * K - 1)

/-- Scalar multiplication does not increase a polynomial's degree. -/
theorem degree_C_mul_le {F : Type*} [Field F] (c : F) (P : F[X]) :
    (C c * P).degree ≤ P.degree := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (degree_C_mul hc).le

/-- For ambient words, common-coordinate agreement is the cardinality of the
corresponding filter of the actual domain. -/
theorem commonAgreementCount_eq_card_filter
    {F : Type*} [Field F] [DecidableEq F] (E : Finset F) (f g : F → F) (p r : F[X]) :
    commonAgreementCount E (fun x ↦ f x) (fun x ↦ g x) p r =
      (E.filter fun x ↦ p.eval x = f x ∧ r.eval x = g x).card := by
  classical
  unfold commonAgreementCount Code.agree
  apply Finset.card_bij (fun x _ ↦ x.val)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx
    exact Finset.mem_filter.mpr ⟨x.property, hx.1.symm, hx.2.symm⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hxE, hf, hg⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x, hxE⟩, by simp [hf, hg], rfl⟩

/-- Three Frobenius remainders give two strict-degree explaining polynomials agreeing
with the fixed inputs on every nonzero point of a subgroup of size `2K`. -/
theorem common_polynomial_witnesses
    {F : Type*} [Field F] [CharP F 2]
    (U : AddSubgroup F) [Fintype U] (K : ℕ) (hpow : ∃ m : ℕ, K = 2 ^ m)
    (hcard : Fintype.card U = 2 * K) (θ : F) :
    ∃ p r : F[X], p.degree < K ∧ r.degree < K ∧
      ∀ x : U, (x : F) ≠ 0 →
        p.eval (x : F) = firstWord K θ x ∧ r.eval (x : F) = secondWord K (x : F) := by
  obtain ⟨m, rfl⟩ := hpow
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
  have h4 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by simp only [pow_succ]; omega
  have h8 : 2 ^ (m + 1 + 2) = 8 * 2 ^ m := by
    rw [show m + 1 + 2 = (m + 1 + 1) + 1 by omega, pow_succ, h4]
    omega
  have hc : Fintype.card U = 2 ^ (m + 1) := hcard.trans h2.symm
  obtain ⟨R₀, _, hd₀, hz₀, he₀⟩ := subspacePolynomial_exists_frobenius_remainder U m hc 0
  obtain ⟨R₁, _, hd₁, hz₁, he₁⟩ := subspacePolynomial_exists_frobenius_remainder U m hc 1
  obtain ⟨R₂, _, hd₂, hz₂, he₂⟩ := subspacePolynomial_exists_frobenius_remainder U m hc 2
  refine ⟨R₂.divX + C θ * R₁.divX, R₀.divX, ?_,
    degree_divX_lt_of_natDegree_le R₀ _ hd₀, ?_⟩
  · apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact degree_divX_lt_of_natDegree_le R₂ _ hd₂
    · exact (degree_C_mul_le _ _).trans_lt (degree_divX_lt_of_natDegree_le R₁ _ hd₁)
  · intro x hx
    have h₀ := eval_divX_eq_pow_pred R₀ hz₀ (x : F) hx (2 * 2 ^ m) (by positivity)
      (by simpa only [Nat.add_zero, h2] using he₀ x)
    have h₁ := eval_divX_eq_pow_pred R₁ hz₁ (x : F) hx (4 * 2 ^ m) (by positivity)
      (by simpa only [h4] using he₁ x)
    have h₂ := eval_divX_eq_pow_pred R₂ hz₂ (x : F) hx (8 * 2 ^ m) (by positivity)
      (by simpa only [h8] using he₂ x)
    simp only [eval_add, eval_mul, eval_C, h₀, h₁, h₂, firstWord, secondWord, and_self]

/-- Adding a scalar multiple of the second input preserves the same common
coordinates, with the same scalar combination of the two explaining polynomials. -/
theorem common_polynomial_witnesses_shift
    {F : Type*} [Field F] [CharP F 2]
    (U : AddSubgroup F) [Fintype U] (K : ℕ) (hpow : ∃ m : ℕ, K = 2 ^ m)
    (hcard : Fintype.card U = 2 * K) (θ s : F) :
    ∃ p r : F[X], p.degree < K ∧ r.degree < K ∧
      ∀ x : U, (x : F) ≠ 0 →
        p.eval (x : F) = firstWord K θ x + s * secondWord K (x : F) ∧
        r.eval (x : F) = secondWord K (x : F) := by
  obtain ⟨p, r, hp, hr, he⟩ := common_polynomial_witnesses U K hpow hcard θ
  refine ⟨p + C s * r, r, ?_, hr, ?_⟩
  · exact (degree_add_le _ _).trans_lt (max_lt hp ((degree_C_mul_le _ _).trans_lt hr))
  · intro x hx
    obtain ⟨hf, hg⟩ := he x hx
    simp only [eval_add, eval_mul, eval_C, hf, hg, and_self]

/-- A subgroup of size `2K` inside the prescribed domain supplies the attained
common-agreement lower bound `2K-1`; both witnesses match on the same nonzero
coordinates. -/
theorem commonAgreementGE_of_subgroup
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (E : Finset F) (U : AddSubgroup F) (hU : ∀ x ∈ U, x ∈ E)
    (K : ℕ) (hpow : ∃ m : ℕ, K = 2 ^ m)
    (hcard : Nat.card U = 2 * K) (θ s : F) :
    commonAgreementGE E K (fun x ↦ firstWord K θ x + s * secondWord K (x : F))
      (fun x ↦ secondWord K (x : F))
      (2 * K - 1) := by
  classical
  obtain ⟨p, r, hp, hr, hmatch⟩ := common_polynomial_witnesses_shift U K hpow
    (by simpa only [Nat.card_eq_fintype_card] using hcard) θ s
  refine ⟨p, r, hp, hr, ?_⟩
  rw [commonAgreementCount_eq_card_filter E
    (fun x : F ↦ firstWord K θ x + s * secondWord K x) (secondWord K) p r]
  have hucard : (additiveDomain U).card = 2 * K := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hz : (0 : F) ∈ additiveDomain U := by simp [additiveDomain]
  calc
    2 * K - 1 = ((additiveDomain U).erase 0).card := by
      rw [Finset.card_erase_of_mem hz, hucard]
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
      have hxU : x ∈ U := by simpa [additiveDomain] using hmem
      exact Finset.mem_filter.mpr ⟨hU x hxU, hmatch ⟨x, hxU⟩ hne⟩)

/-- The characteristic-two cancellation underlying the quadratic challenges. -/
theorem quadratic_identity
    {F : Type*} [Field F] [CharP F 2] (x a b v θ : F) :
    (x ^ 4 + a * x ^ 2 + b * x + v) ^ 2 +
        (a ^ 2 + θ) * (x ^ 4 + a * x ^ 2 + b * x + v) =
      x ^ 8 + θ * x ^ 4 + (a ^ 3 + b ^ 2 + θ * a) * x ^ 2 +
        (a ^ 2 + θ) * (b * x + v) + v ^ 2 := by
  simp only [CharTwo.add_sq, mul_pow]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- A locator with the stated sparse tail yields an actual strict-degree
explaining polynomial at its quadratic challenge on every nonzero root. -/
theorem quadratic_witness_of_locator_shape
    {F : Type*} [Field F] [CharP F 2]
    (K : ℕ) (hK : 0 < K) (L V : F[X]) (a b θ : F)
    (hL : L = X ^ (4 * K) + C a * X ^ (2 * K) + C b * X ^ K + V)
    (hV : 2 * V.natDegree ≤ K) (hVzero : V.coeff 0 = 0) :
    ∃ H : F[X], H.degree < K ∧ ∀ x : F, x ≠ 0 → L.eval x = 0 →
      H.eval x = firstWord K θ x + (a ^ 3 + b ^ 2 + θ * a) * secondWord K x := by
  let Q := C (a ^ 2 + θ) * (C b * X ^ K + V) + V ^ 2
  have hQdeg : Q.natDegree ≤ K := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (by simp)
      · omega
    · exact natDegree_pow_le.trans hV
  have hQzero : Q.coeff 0 = 0 := by
    simp [Q, coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero V, hVzero,
      Nat.ne_of_gt hK]
  refine ⟨Q.divX, degree_divX_lt_of_natDegree_le Q K hQdeg, ?_⟩
  intro x hx hroot
  have hLeval : (x ^ K) ^ 4 + a * (x ^ K) ^ 2 + b * x ^ K + V.eval x = 0 := by
    simpa only [hL, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      ← pow_mul, Nat.mul_comm] using hroot
  have hid := quadratic_identity (x ^ K) a b (V.eval x) θ
  rw [hLeval, zero_pow (by decide), mul_zero, zero_add] at hid
  have heQ : Q.eval x = (x ^ K) ^ 8 + θ * (x ^ K) ^ 4 +
      (a ^ 3 + b ^ 2 + θ * a) * (x ^ K) ^ 2 := by
    have hsum : ((x ^ K) ^ 8 + θ * (x ^ K) ^ 4 +
        (a ^ 3 + b ^ 2 + θ * a) * (x ^ K) ^ 2) +
        ((a ^ 2 + θ) * (b * x ^ K + V.eval x) + V.eval x ^ 2) = 0 := by
      simpa only [add_assoc] using hid.symm
    have := eq_neg_of_add_eq_zero_right hsum
    simpa only [Q, eval_add, eval_mul, eval_C, eval_pow, eval_X, CharTwo.neg_eq] using this
  apply mul_right_cancel₀ hx
  rw [eval_divX_mul_of_coeff_zero Q hQzero x, heQ]
  simp only [firstWord, secondWord, add_mul, mul_assoc,
    pow_sub_one_mul (by omega : 8 * K ≠ 0), pow_sub_one_mul (by omega : 4 * K ≠ 0),
    pow_sub_one_mul (by omega : 2 * K ≠ 0)]
  simp only [← pow_mul, Nat.mul_comm]

/-- Every size-`4K` binary subgroup provides a strict-degree explaining
polynomial at the challenge formed from its top two nonleading coefficients. -/
theorem quadratic_polynomial_witness
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ m : ℕ, K = 2 ^ m) (hcard : Fintype.card W = 4 * K) (θ : F) :
    ∃ H : F[X], H.degree < K ∧ ∀ x : W, (x : F) ≠ 0 →
      H.eval (x : F) = firstWord K θ x +
        ((subspacePolynomial W).coeff (2 * K) ^ 3 + (subspacePolynomial W).coeff K ^ 2 +
          θ * (subspacePolynomial W).coeff (2 * K)) * secondWord K (x : F) := by
  obtain ⟨k, rfl⟩ := hpow
  cases k with
  | zero => simp at hK
  | succ m =>
    have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]
    have h4 : 2 ^ (m + 3) = 4 * 2 ^ (m + 1) := by
      rw [pow_succ, h2]
      omega
    obtain ⟨V, hV, hVzero, hshape⟩ := subspacePolynomial_three_term_shape W m
      (hcard.trans h4.symm)
    obtain ⟨H, hH, hmatch⟩ := quadratic_witness_of_locator_shape (2 ^ (m + 1))
      (by positivity) (subspacePolynomial W) V
      ((subspacePolynomial W).coeff (2 * 2 ^ (m + 1)))
      ((subspacePolynomial W).coeff (2 ^ (m + 1))) θ
      (by simpa only [h4, h2] using hshape)
      (by rw [pow_succ]; omega) hVzero
    refine ⟨H, hH, ?_⟩
    intro x hx
    exact hmatch x hx ((subspacePolynomial_eval_eq_zero_iff W (x : F)).mpr x.property)

/-- Shifting the first input translates each challenge by the same scalar
in characteristic two. -/
theorem shifted_combination
    {F : Type*} [Field F] [CharP F 2] (f g z s : F) :
    (f + s * g) + (z + s) * g = f + z * g := by
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- Each size-`4K` subgroup contained in the actual coordinate domain yields
an exceptional challenge with at least `4K-1` agreements, for the same shifted pair. -/
theorem bad_challenge_of_subgroup
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (E : Finset F) (W : AddSubgroup F) [Fintype W] (hW : ∀ x ∈ W, x ∈ E)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ m : ℕ, K = 2 ^ m)
    (hcard : Nat.card W = 4 * K) (θ s : F) :
    ((subspacePolynomial W).coeff (2 * K) ^ 3 + (subspacePolynomial W).coeff K ^ 2 +
        θ * (subspacePolynomial W).coeff (2 * K)) + s ∈
      badChallenges E K (fun x ↦ firstWord K θ x + s * secondWord K (x : F))
        (fun x ↦ secondWord K (x : F)) (4 * K - 1) := by
  classical
  obtain ⟨H, hH, hmatch⟩ := quadratic_polynomial_witness W K hK hpow
    (by simpa only [Nat.card_eq_fintype_card] using hcard) θ
  rw [mem_badChallenges]
  refine ⟨H, hH, ?_⟩
  let z := (subspacePolynomial W).coeff (2 * K) ^ 3 +
    (subspacePolynomial W).coeff K ^ 2 + θ * (subspacePolynomial W).coeff (2 * K)
  change 4 * K - 1 ≤ agreementCount E
    (fun x ↦ (firstWord K θ x + s * secondWord K (x : F)) +
      (z + s) * secondWord K (x : F)) H
  simp_rw [shifted_combination]
  rw [agreementCount_eq_card_filter E (fun x : F ↦ firstWord K θ x + z * secondWord K x) H]
  have hwcard : (additiveDomain W).card = 4 * K := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hz : (0 : F) ∈ additiveDomain W := by simp [additiveDomain]
  calc
    4 * K - 1 = ((additiveDomain W).erase 0).card := by
      rw [Finset.card_erase_of_mem hz, hwcard]
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
      have hxW : x ∈ W := by simpa [additiveDomain] using hmem
      exact Finset.mem_filter.mpr ⟨hW x hxW, hmatch ⟨x, hxW⟩ hne⟩)

end QuadraticConstruction

end BinaryFieldCounterexamples
