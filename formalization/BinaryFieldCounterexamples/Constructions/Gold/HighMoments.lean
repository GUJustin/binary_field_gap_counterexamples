/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Moments
/-!
# The two-sided Gold support interval

Frobenius-weighted tensor coefficients turn the upward recurrence into a
downward vanishing argument. The top coefficient is a scaled Gold moment;
squaring moves one step upward and adds just one further moment. Combined
with the low-coefficient expansion, this proves the full Frobenius support
interval `[t, d-t]` for the additive derivative on any prescribed binary
domain of dimension `d`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Frobenius-weighted tensor coefficients interpolate between derivative coefficients and moments. -/
noncomputable def weightedCoefficient (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (i r : ℕ) : B :=
  ∑ ij : TensorIndex d, algebraMap (ZMod 2) B (A ij) *
    ((v ij.val.1 : B)^(2^r) * (parameterPolynomial D (v ij.val.2)).coeff (2^i) +
      (v ij.val.2 : B)^(2^r) * (parameterPolynomial D (v ij.val.1)).coeff (2^i))
/-- Weight one gives the actual additive-derivative coefficient. -/
theorem weightedCoefficient_one (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (i : ℕ) :
    weightedCoefficient D v A i 1 = (tensorLinearPart D v A).coeff (2^i) := by
  simp only [weightedCoefficient, tensorLinearPart, finsetSum_coeff, coeff_C_mul, coeff_add]
  norm_num
/-- At the largest binary exponent, weighted coefficients are scaled moments. -/
theorem weightedCoefficient_top (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (r : ℕ) :
    weightedCoefficient D v A k r = normalizingRoot D * goldMoment D v A r := by
  simp only [weightedCoefficient, parameterPolynomial_top_coeff D k hD, goldMoment,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  ring
/-- One upward coefficient step moves the Frobenius weight and adds exactly one Gold moment. -/
theorem weightedCoefficient_recurrence (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (i r : ℕ) :
    weightedCoefficient D v A (i+1) (r+1) = weightedCoefficient D v A i r ^ 2 +
      (normalizedLocator D).coeff (2^(i+1)) * goldMoment D v A r ^ 2 := by
  simp only [weightedCoefficient, parameterPolynomial_coeff_recurrence, goldMoment]
  rw [sum_pow_char, sum_pow_char]
  simp only [mul_pow, binaryScalar_sq, CharTwo.add_sq, ← pow_mul, ← pow_succ,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  ring
/-- Vanishing consecutive moments propagates zero coefficients downward from the top. -/
theorem weightedCoefficient_eq_zero_of_moments (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (s i r : ℕ) (hki : i+s=k)
    (hM : ∀ j, r ≤ j → j ≤ r+s → goldMoment D v A j = 0) :
    weightedCoefficient D v A i r = 0 := by
  induction s generalizing i r with
  | zero =>
    have hi : i = k := by omega
    subst i
    rw [weightedCoefficient_top D k hD, hM r (le_refl _) (by omega), mul_zero]
  | succ s ih =>
    have hnext : weightedCoefficient D v A (i+1) (r+1) = 0 :=
      ih (i+1) (r+1) (by omega) (fun j hj hj' ↦ hM j (by omega) (by omega))
    rw [weightedCoefficient_recurrence, hM r (le_refl _) (by omega), zero_pow (by decide),
      mul_zero, add_zero] at hnext
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hnext
/-- Initial moment vanishing removes the high binary exponents as well as the low ones. -/
theorem tensorLinearPart_high_coeff_eq_zero (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (i s : ℕ) (his : i+s=k) (hs : s+1<t) :
    (tensorLinearPart D v A).coeff (2^i) = 0 := by
  rw [← weightedCoefficient_one]
  exact weightedCoefficient_eq_zero_of_moments D k hD v A s i 1 his
    (fun j hj hj' ↦ hM j hj (by omega))
/-- The additive derivative cannot have exponents beyond the canonical half-domain bound. -/
theorem tensorLinearPart_coeff_eq_zero_above_half (D : AddSubgroup B)
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (n : ℕ) (hn : Nat.card D / 2 < n) : (tensorLinearPart D v A).coeff n = 0 := by
  simp only [tensorLinearPart, finsetSum_coeff, coeff_C_mul, coeff_add]
  apply Finset.sum_eq_zero
  intro ij _
  rw [coeff_eq_zero_of_natDegree_lt ((parameterPolynomial_support_and_degree D _).2.trans_lt hn),
    coeff_eq_zero_of_natDegree_lt ((parameterPolynomial_support_and_degree D _).2.trans_lt hn)]
  ring
/-- Initial moments confine the exact Frobenius support to the Gold interval. -/
theorem tensorLinearPart_support_interval (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (n : ℕ) (hn : n ∈ (tensorLinearPart D v A).support) :
    ∃ i : ℕ, n = 2^i ∧ t ≤ i ∧ i ≤ k+1-t := by
  obtain ⟨i, rfl⟩ := tensorLinearPart_support D v A n hn
  have hne := mem_support_iff.mp hn
  have hlo : t ≤ i := by
    by_contra h
    exact hne (tensorLinearPart_coeff_eq_zero D v A t hM i (by omega))
  have hi : i ≤ k := by
    by_contra h
    apply hne
    apply tensorLinearPart_coeff_eq_zero_above_half
    rw [hD, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨i, rfl, hlo, ?_⟩
  by_contra h
  apply hne
  exact tensorLinearPart_high_coeff_eq_zero D k hD v A t hM i (k-i) (by omega) (by omega)
/-- Moment vanishing yields the required upper degree bound for the additive derivative. -/
theorem tensorLinearPart_natDegree_le (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) :
    (tensorLinearPart D v A).natDegree ≤ 2^(k+1-t) := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra hne
  obtain ⟨i, rfl, _, hi⟩ := tensorLinearPart_support_interval D k hD v A t hM n
    (mem_support_iff.mpr hne)
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) hi)) hn

end BinaryFieldCounterexamples.Gold
